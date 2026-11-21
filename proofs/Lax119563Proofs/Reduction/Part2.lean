import Lax119563Proofs.Hardness.Part1
import Lax119563Proofs.Reduction.Part1

/-! ### Formerly `Lax119563Proofs.Reduction.GLang` -/

section Reduction_GLang

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

end Reduction_GLang

/-! ### Formerly `Lax119563Proofs.Reduction.GSpec` -/

section Reduction_GSpec

/-!
# Specification of compiled generators

`Gn.spec`: if the registers below `d` outside the counter levels `A` hold the stack `ρ`
(`ρ.length = d`), the values fit below `B` (`2 B ≤ 2 ^ w`) and `d + need ≤ R`, then the
compiled generator is `Good`: in emitting mode it emits `g.out x ρ`, in counting mode
`some a` it emits nothing and adds the length of `g.out x ρ` to register `a`; the cost is at
most `κ w * g.cost x ρ`.
-/

namespace Lax119563Proofs.Reduction

variable {R : ℕ} {x : List Bool} {w : ℕ}

namespace Gn

/-- The preconditions of `spec`. -/
structure Pre (R : ℕ) (m : Option ℕ) (A : List ℕ) (d : ℕ) (ρ : List ℕ)
    (env : Fin (R + 1) → ℕ) : Prop where
  len : ρ.length = d
  hA : ∀ i ∈ A, i < d ∧ ρ.getD i 0 = 0
  hm : ∀ a, m = some a → a ∈ A
  agree : ∀ i < d, i ∉ A → env (rg R i) = ρ.getD i 0

/-- The statement of `spec` for one generator. -/
def SpecAt (x : List Bool) (w B R : ℕ) (g : Gn) : Prop :=
  ∀ (m : Option ℕ) (A : List ℕ) (d : ℕ) (ρ : List ℕ) (env : Fin (R + 1) → ℕ),
    Pre R m A d ρ env → d + g.need ≤ R → g.Fits x B ρ →
    (∀ a, m = some a → env (rg R a) + (g.out x ρ).length < B) →
    Good x w (comp R m A d g) env (if m.isSome then [] else g.out x ρ) (κ w * g.cost x ρ) ∧
      ∀ a, m = some a →
        (Stm.exec x (comp R m A d g) env).1 (rg R a) = env (rg R a) + (g.out x ρ).length

lemma Pre.acc_lt {m : Option ℕ} {A : List ℕ} {d : ℕ} {ρ : List ℕ} {env : Fin (R + 1) → ℕ}
    (P : Pre R m A d ρ env) {a : ℕ} (ha : m = some a) : a < d := (P.hA a (P.hm a ha)).1

lemma Pre.hA0 {m : Option ℕ} {A : List ℕ} {d : ℕ} {ρ : List ℕ} {env : Fin (R + 1) → ℕ}
    (P : Pre R m A d ρ env) : ∀ i ∈ A, ρ.getD i 0 = 0 := fun i hi => (P.hA i hi).2

/-- Changing registers that are not stack registers keeps the preconditions. -/
lemma Pre.frame {m : Option ℕ} {A : List ℕ} {d : ℕ} {ρ : List ℕ} {env env' : Fin (R + 1) → ℕ}
    (P : Pre R m A d ρ env) (h : ∀ i < d, i ∉ A → env' (rg R i) = env (rg R i)) :
    Pre R m A d ρ env' :=
  ⟨P.len, P.hA, P.hm, fun i hi hiA => (h i hi hiA).trans (P.agree i hi hiA)⟩

/-- Pushing values. -/
lemma Pre.push {m : Option ℕ} {A : List ℕ} {d : ℕ} {ρ : List ℕ} {env : Fin (R + 1) → ℕ}
    (P : Pre R m A d ρ env) (l : List ℕ)
    (hl : ∀ j < l.length, env (rg R (d + j)) = l.getD j 0) :
    Pre R m A (d + l.length) (ρ ++ l) env := by
  refine ⟨by simp [P.len], fun i hi => ?_, P.hm, fun i hi hiA => ?_⟩
  · have := P.hA i hi
    refine ⟨by omega, ?_⟩
    rw [List.getD_append _ _ _ _ (by rw [P.len]; exact this.1)]; exact this.2
  · by_cases h' : i < d
    · rw [List.getD_append _ _ _ _ (by rw [P.len]; exact h')]; exact P.agree i h' hiA
    · obtain ⟨j, rfl⟩ : ∃ j, i = d + j := ⟨i - d, by omega⟩
      rw [List.getD_append_right _ _ _ _ (by rw [P.len]; omega), P.len,
        show d + j - d = j by omega]
      exact hl j (by omega)

lemma flatMap_range_length_le {f : ℕ → List ℕ} {k L : ℕ} (h : k ≤ L) :
    ((List.range k).flatMap f).length ≤ ((List.range L).flatMap f).length := by
  obtain ⟨j, rfl⟩ : ∃ j, L = k + j := ⟨L - k, by omega⟩
  rw [List.range_add, List.flatMap_append, List.length_append]; omega

lemma flatMap_range_succ_length (f : ℕ → List ℕ) (k : ℕ) :
    ((List.range (k + 1)).flatMap f).length = ((List.range k).flatMap f).length + (f k).length := by
  rw [List.range_succ, List.flatMap_append, List.length_append, List.flatMap_singleton]

lemma ite_isSome_flatMap {β : Type} (m : Option ℕ) (l : List β) (f : β → List ℕ) :
    (l.flatMap fun k => if m.isSome then [] else f k) = if m.isSome then [] else l.flatMap f := by
  cases m <;> simp

lemma κ_sum (w : ℕ) (s : Finset ℕ) (f : ℕ → ℕ) (c : ℕ) (hc : c ≤ κ w) :
    ∑ k ∈ s, (κ w * f k + c) ≤ κ w * ∑ k ∈ s, (f k + 1) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => by rw [Nat.mul_add, Nat.mul_one]; omega

lemma frame_lt {m : Option ℕ} {A : List ℕ} {d : ℕ} {ρ : List ℕ} {env : Fin (R + 1) → ℕ}
    (P : Pre R m A d ρ env) (hdR : d < R) (g : Gn) {d' : ℕ} (hd : d ≤ d') {i : ℕ} (hi : i < d)
    (hiA : i ∉ A) (env' : Fin (R + 1) → ℕ) :
    (Stm.exec x (comp R m A d' g) env').1 (rg R i) = env' (rg R i) :=
  comp_frame (j := i) g (by omega) (by omega)
    (fun a ha hai => hiA (by rw [← hai]; exact P.hm a ha))
    (fun a ha => by have := P.acc_lt ha; omega) env'

lemma frame_acc {m : Option ℕ} {A : List ℕ} {d : ℕ} {ρ : List ℕ} {env : Fin (R + 1) → ℕ}
    (P : Pre R m A d ρ env) (hdR : d < R) (e : Xp) {a : ℕ} (ha : m = some a) {t : ℕ}
    (ht : d ≤ t) (env' : Fin (R + 1) → ℕ) :
    (Stm.exec x (e.comp R d A t) env').1 (rg R a) = env' (rg R a) := by
  have := P.acc_lt ha
  exact Xp.comp_frame e (by omega) (by omega) env'

lemma xframe {m : Option ℕ} {A : List ℕ} {d : ℕ} {ρ : List ℕ} {env : Fin (R + 1) → ℕ}
    (P : Pre R m A d ρ env) (hdR : d < R) (e : Xp) {t : ℕ} (ht : d ≤ t)
    (env' : Fin (R + 1) → ℕ) (i : ℕ) (hi : i < d) :
    (Stm.exec x (e.comp R d A t) env').1 (rg R i) = env' (rg R i) :=
  Xp.comp_frame e (by omega) (by omega) env'

lemma one_le_need : ∀ g : Gn, 1 ≤ g.need
  | skip => le_rfl
  | emit e => Xp.one_le_need e
  | seq g _ => le_trans (one_le_need g) (le_max_left _ _)
  | ite c _ _ => le_trans (Xp.one_le_need c) (le_max_left _ _)
  | bind e _ => le_trans (Xp.one_le_need e) (le_max_left _ _)
  | loop .. => by simp only [need]; omega
  | loopX .. => by simp only [need]; omega
  | len _ => by simp only [need]; omega
  | log .. => by simp only [need]; omega
  | count .. => by simp only [need]; omega

/-! ### The cases -/

variable {B : ℕ}

lemma spec_skip : SpecAt x w B R skip := by
  intro m A d ρ env P hR hf hc
  have K := Xp.κ_ge w
  refine ⟨Good.skip.of_eq (by cases m <;> rfl) (by simp [cost]; omega), fun a _ => ?_⟩
  simp [comp, Stm.exec, out]

lemma spec_emit (hB : 2 * B ≤ 2 ^ w) (e : Xp) : SpecAt x w B R (emit e) := by
  intro m A d ρ env P hR hf hc
  have K := Xp.κ_ge w
  cases m with
  | none =>
    obtain ⟨G, v⟩ := Xp.spec (x := x) hB P.len P.hA0 e d env le_rfl hR P.agree hf
    have hv := Xp.eval_lt hf
    refine ⟨(G.seq (Good.emit (by simp only [Ex.Fits, v]; omega))).of_eq
      (by simp [Ex.eval, v, out]) ?_, fun a ha => by cases ha⟩
    simp only [cost, Ex.size, Nat.mul_add, Nat.mul_one]; omega
  | some a =>
    have h1 := hc a rfl
    simp only [out, List.length_singleton] at h1
    refine ⟨(Good.set ?_).of_eq rfl ?_, fun a' ha' => ?_⟩
    · simp only [Ex.Fits, Ex.eval]; omega
    · simp only [cost, Ex.size, Nat.mul_add, Nat.mul_one]; omega
    · cases ha'
      simp [comp, incr, exec_set_fst, Ex.eval, out]

lemma spec_seq (g h : Gn) (ihg : SpecAt x w B R g) (ihh : SpecAt x w B R h) :
    SpecAt x w B R (seq g h) := by
  intro m A d ρ env P hR hf hc
  simp only [need] at hR
  have hdR : d < R := by have := one_le_need g; omega
  obtain ⟨G1, a1⟩ := ihg m A d ρ env P (by omega) hf.1 (fun a ha => by
    have := hc a ha; simp only [out, List.length_append] at this; omega)
  have P1 := P.frame (env' := (Stm.exec x (comp R m A d g) env).1)
    (fun i hi hiA => frame_lt P hdR g le_rfl hi hiA env)
  obtain ⟨G2, a2⟩ := ihh m A d ρ _ P1 (by omega) hf.2 (fun a ha => by
    have := hc a ha; rw [a1 a ha]; simp only [out, List.length_append] at this; omega)
  refine ⟨(G1.seq G2).of_eq (by cases m <;> simp [out]) (by simp [cost, Nat.mul_add]),
    fun a ha => ?_⟩
  simp only [comp, exec_seq_fst, out, List.length_append]
  rw [a2 a ha, a1 a ha]; omega

lemma spec_ite (hB : 2 * B ≤ 2 ^ w) (c : Xp) (g h : Gn) (ihg : SpecAt x w B R g)
    (ihh : SpecAt x w B R h) : SpecAt x w B R (ite c g h) := by
  intro m A d ρ env P hR hf hc
  have K := Xp.κ_ge w
  simp only [need] at hR
  have hdR : d < R := by have := Xp.one_le_need c; omega
  obtain ⟨G0, v0⟩ := Xp.spec (x := x) hB P.len P.hA0 c d env le_rfl (by omega) P.agree hf.1
  have hcv := Xp.eval_lt hf.1
  set env1 := (Stm.exec x (c.comp R d A d) env).1 with he1
  have P1 := P.frame (env' := env1) (fun i hi _ => xframe P hdR c le_rfl env i hi)
  have hfit : Ex.Fits w env1 (.var (rg R d) : Ex (R + 1)) := by
    simp only [Ex.Fits, v0]; omega
  have hacc : ∀ a, m = some a → env1 (rg R a) = env (rg R a) :=
    fun a ha => frame_acc P hdR c ha le_rfl env
  by_cases hp : c.eval ρ ≠ 0
  · have hf' : g.Fits x B ρ := by have := hf.2; rwa [if_pos hp] at this
    obtain ⟨G, a1⟩ := ihg m A d ρ env1 P1 (by omega) hf' (fun a ha => by
      have := hc a ha; rw [hacc a ha]; simpa [out, if_pos hp] using this)
    have hcond : (Ex.var (rg R d) : Ex (R + 1)).eval env1 ≠ 0 := by simpa [Ex.eval, v0] using hp
    refine ⟨(G0.seq (Good.iteT hfit hcond G)).of_eq (by simp [out, if_pos hp]) ?_,
      fun a ha => ?_⟩
    · simp only [cost, if_pos hp, Ex.size, Nat.mul_add, Nat.mul_one]; omega
    · simp only [comp, exec_seq_fst]
      rw [← he1]
      simp only [Stm.exec, if_pos hcond]
      rw [a1 a ha, hacc a ha]; simp [out, if_pos hp]
  · have hf' : h.Fits x B ρ := by have := hf.2; rwa [if_neg hp] at this
    obtain ⟨G, a1⟩ := ihh m A d ρ env1 P1 (by omega) hf' (fun a ha => by
      have := hc a ha; rw [hacc a ha]; simpa [out, if_neg hp] using this)
    have hcond : (Ex.var (rg R d) : Ex (R + 1)).eval env1 = 0 := by
      simp only [Ex.eval, v0]; simpa using hp
    refine ⟨(G0.seq (Good.iteF hfit hcond G)).of_eq (by simp [out, if_neg hp]) ?_,
      fun a ha => ?_⟩
    · simp only [cost, if_neg hp, Ex.size, Nat.mul_add, Nat.mul_one]; omega
    · simp only [comp, exec_seq_fst]
      rw [← he1]
      simp only [Stm.exec, hcond, ne_eq, not_true_eq_false, if_false]
      rw [a1 a ha, hacc a ha]; simp [out, if_neg hp]

lemma spec_bind (hB : 2 * B ≤ 2 ^ w) (e : Xp) (g : Gn) (ihg : SpecAt x w B R g) :
    SpecAt x w B R (bind e g) := by
  intro m A d ρ env P hR hf hc
  simp only [need] at hR
  have hdR : d < R := by have := Xp.one_le_need e; omega
  obtain ⟨G0, v0⟩ := Xp.spec (x := x) hB P.len P.hA0 e d env le_rfl (by omega) P.agree hf.1
  set env1 := (Stm.exec x (e.comp R d A d) env).1 with he1
  have P1 := (P.frame (env' := env1) (fun i hi _ => xframe P hdR e le_rfl env i hi)).push
    [e.eval ρ] (fun j hj => by
      simp only [List.length_singleton] at hj
      obtain rfl : j = 0 := by omega
      simpa using v0)
  have hacc : ∀ a, m = some a → env1 (rg R a) = env (rg R a) :=
    fun a ha => frame_acc P hdR e ha le_rfl env
  obtain ⟨G, a1⟩ := ihg m A (d + 1) _ env1 P1 (by omega) hf.2 (fun a ha => by
    have := hc a ha; rw [hacc a ha]; simpa [out] using this)
  refine ⟨(G0.seq G).of_eq (by simp [out]) (by simp [cost, Nat.mul_add]), fun a ha => ?_⟩
  simp only [comp, exec_seq_fst, List.length_singleton]
  rw [← he1, a1 a ha, hacc a ha]; rfl

lemma spec_loop (hB : 2 * B ≤ 2 ^ w) (lim : Xp) (g : Gn) (ihg : SpecAt x w B R g) :
    SpecAt x w B R (loop lim g) := by
  intro m A d ρ env P hR hf hc
  have K := Xp.κ_ge w
  simp only [need] at hR
  have hdR : d < R := by have := Xp.one_le_need lim; omega
  obtain ⟨G0, v0⟩ := Xp.spec (x := x) hB P.len P.hA0 lim d env le_rfl (by omega) P.agree hf.1
  have hLB := Xp.eval_lt hf.1
  set L := lim.eval ρ with hLdef
  set env1 := (Stm.exec x (lim.comp R d A d) env).1 with he1
  have hacc : ∀ a, m = some a → env1 (rg R a) = env (rg R a) :=
    fun a ha => frame_acc P hdR lim ha le_rfl env
  obtain ⟨F, hF⟩ : ∃ F : ℕ → List ℕ, F = fun k => g.out x (ρ ++ [L, k]) := ⟨_, rfl⟩
  have hFk : ∀ k, g.out x (ρ ++ [L, k]) = F k := fun k => by rw [hF]
  have hout : (loop lim g).out x ρ = (List.range L).flatMap F := by rw [hF]; rfl
  have n1 : rg R (d + 1) ≠ rg R d := rg_ne (by omega) (by omega)
  have hInv := Stm.good_loopInvT (x := x) (w := w) (i := rg R (d + 1)) (lim := rg R d)
    (body := comp R m A (d + 2) g) (env := env1)
    (fun k e => (∀ i < d, i ∉ A → e (rg R i) = ρ.getD i 0) ∧ e (rg R d) = L ∧
      ∀ a, m = some a → e (rg R a) = env1 (rg R a) + ((List.range k).flatMap F).length)
    (fun k => if m.isSome then [] else F k) (fun k => κ w * g.cost x (ρ ++ [L, k]))
    (by rw [v0]; omega)
    ⟨fun i hi hiA => (xframe P hdR lim le_rfl env i hi).trans (P.agree i hi hiA), v0,
      fun a _ => by simp⟩ (by
      intro k hk e ⟨h1, h2, h3⟩
      rw [v0] at hk
      have hne : ∀ i < d, rg R i ≠ rg R (d + 1) := fun i hi => rg_ne (by omega) (by omega)
      have P' : Pre R m A (d + 2) (ρ ++ [L, k]) (Function.update e (rg R (d + 1)) k) := by
        have P0 : Pre R m A d ρ (Function.update e (rg R (d + 1)) k) :=
          ⟨P.len, P.hA, P.hm, fun i hi hiA => by
            rw [Function.update_of_ne (hne i hi)]; exact h1 i hi hiA⟩
        refine P0.push [L, k] (fun j hj => ?_)
        simp only [List.length_cons, List.length_nil] at hj
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
        · simpa [Function.update_of_ne n1.symm] using h2
        · simp
      obtain ⟨G, a1⟩ := ihg m A (d + 2) _ _ P' (by omega) (hf.2 k hk) (fun a ha => by
        have hlt := P.acc_lt ha
        rw [Function.update_of_ne (hne a hlt), h3 a ha, hacc a ha, hFk]
        have h1 := hc a ha
        have h2 := flatMap_range_length_le (f := F) (show k + 1 ≤ L by omega)
        rw [flatMap_range_succ_length] at h2
        rw [hout] at h1; omega)
      rw [hFk] at G a1
      refine ⟨G, ?_, ?_, ?_⟩
      · intro i hi hiA
        rw [frame_lt P hdR g (by omega) hi hiA, Function.update_of_ne (hne i hi)]
        exact h1 i hi hiA
      · rw [comp_frame (j := d) g (by omega) (by omega)
          (fun a ha hai => by have := P.acc_lt ha; omega)
          (fun a ha => by have := P.acc_lt ha; omega),
          Function.update_of_ne n1.symm, h2]
      · intro a ha
        have hlt := P.acc_lt ha
        rw [a1 a ha, Function.update_of_ne (hne a hlt), h3 a ha, flatMap_range_succ_length]
        omega)
  rw [v0] at hInv
  obtain ⟨GLp, HL⟩ := hInv
  refine ⟨(G0.seq GLp).of_eq (by rw [ite_isSome_flatMap]; cases m <;> simp [hout]) ?_,
    fun a ha => ?_⟩
  · have h1 := κ_sum w (Finset.range L) (fun k => g.cost x (ρ ++ [L, k]))
      (4 * unitCost w + 1) (by omega)
    simp only [cost, ← hLdef, Nat.mul_add, Nat.mul_one]
    have e1 : ∑ k ∈ Finset.range L, (κ w * g.cost x (ρ ++ [L, k]) + 4 * unitCost w + 1) =
        ∑ k ∈ Finset.range L, (κ w * g.cost x (ρ ++ [L, k]) + (4 * unitCost w + 1)) :=
      Finset.sum_congr rfl fun _ _ => by ring
    omega
  · have hlt := P.acc_lt ha
    show (Stm.exec x (Stm.loop (rg R (d + 1)) (rg R d) (comp R m A (d + 2) g)) env1).1
      (rg R a) = _
    rw [Stm.exec_loop_fst, Function.update_of_ne (rg_ne (by omega) (by omega)), v0,
      HL.2.2 a ha, hacc a ha, hout]

lemma spec_loopX (hB : 2 * B ≤ 2 ^ w) (lim : Xp) (g : Gn) (ihg : SpecAt x w B R g) :
    SpecAt x w B R (loopX lim g) := by
  intro m A d ρ env P hR hf hc
  have K := Xp.κ_ge w
  simp only [need] at hR
  have hdR : d < R := by have := Xp.one_le_need lim; omega
  obtain ⟨G0, v0⟩ := Xp.spec (x := x) hB P.len P.hA0 lim d env le_rfl (by omega) P.agree hf.1
  have hLB := Xp.eval_lt hf.1
  set L := lim.eval ρ with hLdef
  set env1 := (Stm.exec x (lim.comp R d A d) env).1 with he1
  have hacc : ∀ a, m = some a → env1 (rg R a) = env (rg R a) :=
    fun a ha => frame_acc P hdR lim ha le_rfl env
  obtain ⟨F, hF⟩ : ∃ F : ℕ → List ℕ, F = fun k => g.out x (ρ ++ [L, k, inBit x k]) :=
    ⟨_, rfl⟩
  have hFk : ∀ k, g.out x (ρ ++ [L, k, inBit x k]) = F k := fun k => by rw [hF]
  have hout : (loopX lim g).out x ρ = (List.range L).flatMap F := by rw [hF]; rfl
  have n1 : rg R (d + 1) ≠ rg R d := rg_ne (by omega) (by omega)
  have n2 : rg R (d + 2) ≠ rg R d := rg_ne (by omega) (by omega)
  have n21 : rg R (d + 2) ≠ rg R (d + 1) := rg_ne (by omega) (by omega)
  have hInv := Stm.good_loopXInvT (x := x) (w := w) (i := rg R (d + 1)) (lim := rg R d)
    (xb := rg R (d + 2)) (body := comp R m A (d + 3) g) (env := env1)
    (fun k e => (∀ i < d, i ∉ A → e (rg R i) = ρ.getD i 0) ∧ e (rg R d) = L ∧
      ∀ a, m = some a → e (rg R a) = env1 (rg R a) + ((List.range k).flatMap F).length)
    (fun k => if m.isSome then [] else F k)
    (fun k => κ w * g.cost x (ρ ++ [L, k, inBit x k]))
    (by rw [v0]; omega)
    ⟨fun i hi hiA => (xframe P hdR lim le_rfl env i hi).trans (P.agree i hi hiA), v0,
      fun a _ => by simp⟩ (by
      intro k hk e ⟨h1, h2, h3⟩
      rw [v0] at hk
      have hne : ∀ i < d, rg R i ≠ rg R (d + 1) := fun i hi => rg_ne (by omega) (by omega)
      have hne2 : ∀ i < d, rg R i ≠ rg R (d + 2) := fun i hi => rg_ne (by omega) (by omega)
      set e' := Function.update (Function.update e (rg R (d + 1)) k) (rg R (d + 2)) (inBit x k)
        with he'
      have e'i : ∀ i < d, e' (rg R i) = e (rg R i) := fun i hi => by
        rw [he', Function.update_of_ne (hne2 i hi), Function.update_of_ne (hne i hi)]
      have P' : Pre R m A (d + 3) (ρ ++ [L, k, inBit x k]) e' := by
        have P0 : Pre R m A d ρ e' :=
          ⟨P.len, P.hA, P.hm, fun i hi hiA => by rw [e'i i hi]; exact h1 i hi hiA⟩
        refine P0.push [L, k, inBit x k] (fun j hj => ?_)
        simp only [List.length_cons, List.length_nil] at hj
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
        · simpa [he', Function.update_of_ne n2.symm, Function.update_of_ne n1.symm] using h2
        · simpa [he', Function.update_of_ne n21.symm]
        · simp [he']
      obtain ⟨G, a1⟩ := ihg m A (d + 3) _ _ P' (by omega) (hf.2 k hk) (fun a ha => by
        have hlt := P.acc_lt ha
        rw [e'i a hlt, h3 a ha, hacc a ha, hFk]
        have h1 := hc a ha
        have h2 := flatMap_range_length_le (f := F) (show k + 1 ≤ L by omega)
        rw [flatMap_range_succ_length] at h2
        rw [hout] at h1; omega)
      rw [hFk] at G a1
      refine ⟨G, ?_, ?_, ?_⟩
      · intro i hi hiA
        rw [frame_lt P hdR g (by omega) hi hiA, e'i i hi]
        exact h1 i hi hiA
      · rw [comp_frame (j := d) g (by omega) (by omega)
          (fun a ha hai => by have := P.acc_lt ha; omega)
          (fun a ha => by have := P.acc_lt ha; omega), he',
          Function.update_of_ne n2.symm, Function.update_of_ne n1.symm, h2]
      · intro a ha
        have hlt := P.acc_lt ha
        rw [a1 a ha, e'i a hlt, h3 a ha, flatMap_range_succ_length]
        omega)
  rw [v0] at hInv
  obtain ⟨GLp, HL⟩ := hInv
  refine ⟨(G0.seq GLp).of_eq (by rw [ite_isSome_flatMap]; cases m <;> simp [hout]) ?_,
    fun a ha => ?_⟩
  · have h1 := κ_sum w (Finset.range L) (fun k => g.cost x (ρ ++ [L, k, inBit x k]))
      (5 * unitCost w + 1) (by omega)
    simp only [cost, ← hLdef, Nat.mul_add, Nat.mul_one]
    have e1 : ∑ k ∈ Finset.range L,
        (unitCost w + κ w * g.cost x (ρ ++ [L, k, inBit x k]) + 4 * unitCost w + 1) =
        ∑ k ∈ Finset.range L, (κ w * g.cost x (ρ ++ [L, k, inBit x k]) + (5 * unitCost w + 1)) :=
      Finset.sum_congr rfl fun _ _ => by ring
    have e2 : unitCost w * x.length ≤ κ w * x.length := Nat.mul_le_mul_right _ (by omega)
    omega
  · have hlt := P.acc_lt ha
    show (Stm.exec x (Stm.loopX (rg R (d + 1)) (rg R d) (rg R (d + 2))
      (comp R m A (d + 3) g)) env1).1 (rg R a) = _
    rw [Stm.exec_loopX_fst, Function.update_of_ne (rg_ne (by omega) (by omega)), v0,
      HL.2.2 a ha, hacc a ha, hout]

lemma spec_len (hB : 2 * B ≤ 2 ^ w) (g : Gn) (ihg : SpecAt x w B R g) :
    SpecAt x w B R (len g) := by
  intro m A d ρ env P hR hf hc
  have K := Xp.κ_ge w
  simp only [need] at hR
  set env1 := Function.update env (rg R d) x.length with he1
  have hne : ∀ i < d, rg R i ≠ rg R d := fun i hi => rg_ne (by omega) (by omega)
  have P1 : Pre R m A (d + 1) (ρ ++ [x.length]) env1 := by
    refine (P.frame (env' := env1) (fun i hi _ => ?_)).push [x.length] (fun j hj => ?_)
    · rw [he1, Function.update_of_ne (hne i hi)]
    · simp only [List.length_singleton] at hj
      obtain rfl : j = 0 := by omega
      simp [he1]
  have hacc : ∀ a, m = some a → env1 (rg R a) = env (rg R a) :=
    fun a ha => by rw [he1, Function.update_of_ne (hne a (P.acc_lt ha))]
  obtain ⟨G, a1⟩ := ihg m A (d + 1) _ env1 P1 (by omega) hf.2 (fun a ha => by
    have := hc a ha; rw [hacc a ha]; simpa [out] using this)
  have hB2 : x.length + 1 < 2 ^ w := by have := hf.1; omega
  refine ⟨((Good.len (r := rg R d) (env := env) hB2).seq G).of_eq (by simp [out]) ?_,
    fun a ha => ?_⟩
  · simp only [cost]
    have e1 : x.length * (5 * unitCost w + 1) ≤ x.length * κ w :=
      Nat.mul_le_mul_left _ (by omega)
    have e3 : x.length * (4 * unitCost w + 1) + unitCost w * (x.length + 1) =
        x.length * (5 * unitCost w + 1) + unitCost w := by ring
    have e4 : κ w * (x.length + 1 + g.cost x (ρ ++ [x.length])) =
        x.length * κ w + κ w + κ w * g.cost x (ρ ++ [x.length]) := by ring
    omega
  · show (Stm.exec x (comp R m A (d + 1) g) env1).1 (rg R a) = _
    rw [a1 a ha, hacc a ha]; rfl

lemma spec_log (hB : 2 * B ≤ 2 ^ w) (e : Xp) (g : Gn) (ihg : SpecAt x w B R g) :
    SpecAt x w B R (log e g) := by
  intro m A d ρ env P hR hf hc
  have K := Xp.κ_ge w
  simp only [need] at hR
  have hdR : d < R := by omega
  obtain ⟨G0, v0⟩ := Xp.spec (x := x) hB P.len P.hA0 e d env le_rfl (by omega) P.agree hf.1
  have hEB := Xp.eval_lt hf.1
  set env1 := (Stm.exec x (e.comp R d A d) env).1 with he1
  have n01 : rg R d ≠ rg R (d + 1) := rg_ne (by omega) (by omega)
  have n02 : rg R d ≠ rg R (d + 2) := rg_ne (by omega) (by omega)
  have n03 : rg R d ≠ rg R (d + 3) := rg_ne (by omega) (by omega)
  have n12 : rg R (d + 1) ≠ rg R (d + 2) := rg_ne (by omega) (by omega)
  have n13 : rg R (d + 1) ≠ rg R (d + 3) := rg_ne (by omega) (by omega)
  have n23 : rg R (d + 2) ≠ rg R (d + 3) := rg_ne (by omega) (by omega)
  obtain ⟨G1, v1, f1⟩ := logS_spec (x := x) n01 n02 n03 n12 n13 n23 (env := env1) hB
    (by rw [v0]; exact hEB)
  rw [v0] at G1 v1
  set env2 := (Stm.exec x (logS (rg R d) (rg R (d + 1)) (rg R (d + 2)) (rg R (d + 3)))
    env1).1 with he2
  have hfr : ∀ i < d, env2 (rg R i) = env (rg R i) := fun i hi => by
    rw [f1 _ (rg_ne (by omega) (by omega)) (rg_ne (by omega) (by omega))
      (rg_ne (by omega) (by omega)) (rg_ne (by omega) (by omega))]
    exact xframe P hdR e le_rfl env i hi
  have P1 : Pre R m A (d + 1) (ρ ++ [Nat.log 2 (e.eval ρ)]) env2 := by
    refine (P.frame (env' := env2) (fun i hi _ => hfr i hi)).push [Nat.log 2 (e.eval ρ)]
      (fun j hj => ?_)
    simp only [List.length_singleton] at hj
    obtain rfl : j = 0 := by omega
    simpa using v1
  have hacc : ∀ a, m = some a → env2 (rg R a) = env (rg R a) :=
    fun a ha => hfr a (P.acc_lt ha)
  obtain ⟨G, a1⟩ := ihg m A (d + 1) _ env2 P1 (by omega) hf.2 (fun a ha => by
    have := hc a ha; rw [hacc a ha]; simpa [out] using this)
  refine ⟨(G0.seq (G1.seq G)).of_eq (by simp [out]) ?_, fun a ha => ?_⟩
  · simp only [cost, Nat.mul_add]; omega
  · show (Stm.exec x (comp R m A (d + 1) g) env2).1 (rg R a) = _
    rw [a1 a ha, hacc a ha]; rfl

lemma spec_count (g h : Gn) (ihg : SpecAt x w B R g) (ihh : SpecAt x w B R h) :
    SpecAt x w B R (count g h) := by
  intro m A d ρ env P hR hf hc
  have K := Xp.κ_ge w
  simp only [need] at hR
  set n := (g.out x (ρ ++ [0])).length with hn
  set env1 := Function.update env (rg R d) 0 with he1
  have hne : ∀ i < d, rg R i ≠ rg R d := fun i hi => rg_ne (by omega) (by omega)
  have Pg : Pre R (some d) (d :: A) (d + 1) (ρ ++ [0]) env1 := by
    refine ⟨by simp [P.len], fun i hi => ?_, fun a ha => by cases ha; simp, fun i hi hiA => ?_⟩
    · rcases List.mem_cons.mp hi with rfl | hi
      · refine ⟨by omega, ?_⟩
        rw [List.getD_append_right _ _ _ _ (by rw [P.len]), P.len]; simp
      · have := P.hA i hi
        refine ⟨by omega, ?_⟩
        rw [List.getD_append _ _ _ _ (by rw [P.len]; exact this.1)]; exact this.2
    · have hid : i < d := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact h
        · exact absurd (List.mem_cons.mpr (Or.inl h)) hiA
      rw [he1, Function.update_of_ne (hne i hid),
        List.getD_append _ _ _ _ (by rw [P.len]; exact hid)]
      exact P.agree i hid (fun h' => hiA (List.mem_cons_of_mem _ h'))
  obtain ⟨Gg, ag⟩ := ihg (some d) (d :: A) (d + 1) _ env1 Pg (by omega) hf.2.1
    (fun a ha => by cases ha; simp [he1]; exact hf.1)
  set env2 := (Stm.exec x (comp R (some d) (d :: A) (d + 1) g) env1).1 with he2
  have hd2 : env2 (rg R d) = n := by rw [ag d rfl]; simp [he1, hn]
  have hfr : ∀ i < d, env2 (rg R i) = env (rg R i) := fun i hi => by
    show (Stm.exec x (comp R (some d) (d :: A) (d + 1) g) env1).1 (rg R i) = _
    rw [comp_frame (j := i) g (by omega) (by omega) (fun a ha hai => by cases ha; omega)
      (fun a ha => by cases ha; omega), he1, Function.update_of_ne (hne i hi)]
  have P1 : Pre R m A (d + 1) (ρ ++ [n]) env2 := by
    refine (P.frame (env' := env2) (fun i hi _ => hfr i hi)).push [n] (fun j hj => ?_)
    simp only [List.length_singleton] at hj
    obtain rfl : j = 0 := by omega
    simpa using hd2
  have hacc : ∀ a, m = some a → env2 (rg R a) = env (rg R a) :=
    fun a ha => hfr a (P.acc_lt ha)
  obtain ⟨Gh, ah⟩ := ihh m A (d + 1) _ env2 P1 (by omega) hf.2.2 (fun a ha => by
    have := hc a ha; rw [hacc a ha]; simpa [out] using this)
  have G1 : Good x w (Stm.set (rg R d) (.const 0)) env [] (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp only [Ex.Fits]; positivity)).of_eq rfl (by simp [Ex.size])
  refine ⟨(G1.seq (Gg.seq Gh)).of_eq (by simp only [out, ← hn]; simp) ?_, fun a ha => ?_⟩
  · simp only [cost, ← hn, Nat.mul_add, Nat.mul_one]; omega
  · show (Stm.exec x (comp R m A (d + 1) h) env2).1 (rg R a) = _
    rw [ah a ha, hacc a ha]; rfl

/-- **Specification of compiled generators.** -/
theorem spec {B : ℕ} (hB : 2 * B ≤ 2 ^ w) (g : Gn) : SpecAt x w B R g := by
  induction g with
  | skip => exact spec_skip
  | emit e => exact spec_emit hB e
  | seq g h ihg ihh => exact spec_seq g h ihg ihh
  | ite c g h ihg ihh => exact spec_ite hB c g h ihg ihh
  | bind e g ih => exact spec_bind hB e g ih
  | loop lim g ih => exact spec_loop hB lim g ih
  | loopX lim g ih => exact spec_loopX hB lim g ih
  | len g ih => exact spec_len hB g ih
  | log e g ih => exact spec_log hB e g ih
  | count g h ihg ihh => exact spec_count g h ihg ihh

end Gn

end Lax119563Proofs.Reduction

end Reduction_GSpec

/-! ### Formerly `Lax119563Proofs.Reduction.GMachine` -/

section Reduction_GMachine

/-!
# Machines of generators

`Gn.computesWithin`: a generator `g` (independent of the input) whose values fit below
`B` with `2 B ≤ 2 ^ w` gives the deterministic machine `Gn.machine R g`, which computes
`encodeNats (g.out x [])` from `x` within `κ w * g.cost x [] + 20 |…| + 4` steps.
-/

open Lax119563.BinaryEncodings Lax119563.DeterministicTime
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Reduction

variable {R : ℕ} {x : List Bool} {w : ℕ}

namespace Gn

/-- Every `loopX` body is free of `loopX` and `len`. -/
def WFX : Gn → Prop
  | seq g h => WFX g ∧ WFX h
  | ite _ g h => WFX g ∧ WFX h
  | bind _ g => WFX g
  | loop _ g => WFX g
  | loopX _ g => NoX g ∧ WFX g
  | len g => WFX g
  | log _ g => WFX g
  | count g h => WFX g ∧ WFX h
  | _ => True

lemma noX_logS {N : ℕ} (L u v c : Fin N) : (logS L u v c).noX = true := rfl

lemma noX_comp (g : Gn) : ∀ (m : Option ℕ) (A : List ℕ) (d : ℕ), g.NoX →
    (comp R m A d g).noX = true := by
  induction g with
  | skip => intro m A d _; rfl
  | emit e =>
    intro m A d _
    cases m with
    | none => simp [comp, Stm.noX, Xp.noX_comp]
    | some a => rfl
  | seq g h ihg ihh => intro m A d h'; simp [comp, Stm.noX, ihg m A d h'.1, ihh m A d h'.2]
  | ite c g h ihg ihh =>
    intro m A d h'; simp [comp, Stm.noX, Xp.noX_comp, ihg m A d h'.1, ihh m A d h'.2]
  | bind e g ih => intro m A d h'; simp [comp, Stm.noX, Xp.noX_comp, ih m A (d + 1) h']
  | loop lim g ih => intro m A d h'; simp [comp, Stm.noX, Xp.noX_comp, ih m A (d + 2) h']
  | loopX lim g ih => intro m A d h'; exact h'.elim
  | len g ih => intro m A d h'; exact h'.elim
  | log e g ih =>
    intro m A d h'; simp [comp, Stm.noX, Xp.noX_comp, noX_logS, ih m A (d + 1) h']
  | count g h ihg ihh =>
    intro m A d h'
    simp [comp, Stm.noX, ihg (some d) (d :: A) (d + 1) h'.1, ihh m A (d + 1) h'.2]

lemma wr_false {g : Gn} {m : Option ℕ} {A : List ℕ} {d j : ℕ} (hj : j < d) (hjR : j < R)
    (hm : ∀ a, m = some a → a ≠ j) (hmR : ∀ a, m = some a → a < R) :
    Stm.wr (comp R m A d g) (rg R j) = false := by
  refine (wrIn_comp g m A d).wr_false ?_
  rintro (h | ⟨a, ha, he⟩)
  · exact not_above hj hjR h
  · exact hm a ha ((rg_inj (hmR a ha) hjR).mp he.symm)

lemma wf_comp (g : Gn) : ∀ (m : Option ℕ) (A : List ℕ) (d : ℕ), g.WFX → d + g.need ≤ R →
    (∀ a, m = some a → a < d) → (comp R m A d g).WF := by
  induction g with
  | skip => intro m A d _ _ _; trivial
  | emit e =>
    intro m A d _ hR _
    cases m with
    | none => exact ⟨Xp.wf_comp e d hR, trivial⟩
    | some a => trivial
  | seq g h ihg ihh =>
    intro m A d hw hR hm; simp only [need] at hR
    exact ⟨ihg m A d hw.1 (by omega) hm, ihh m A d hw.2 (by omega) hm⟩
  | ite c g h ihg ihh =>
    intro m A d hw hR hm; simp only [need] at hR
    exact ⟨Xp.wf_comp c d (by omega), ihg m A d hw.1 (by omega) hm, ihh m A d hw.2 (by omega) hm⟩
  | bind e g ih =>
    intro m A d hw hR hm; simp only [need] at hR
    exact ⟨Xp.wf_comp e d (by omega), ih m A (d + 1) hw (by omega)
      (fun a ha => by have := hm a ha; omega)⟩
  | loop lim g ih =>
    intro m A d hw hR hm; simp only [need] at hR
    refine ⟨Xp.wf_comp lim d (by omega), rg_ne (by omega) (by omega), ?_, ?_,
      ih m A (d + 2) hw (by omega) (fun a ha => by have := hm a ha; omega)⟩
    · exact wr_false (by omega) (by omega) (fun a ha => by have := hm a ha; omega)
        (fun a ha => by have := hm a ha; omega)
    · exact wr_false (by omega) (by omega) (fun a ha => by have := hm a ha; omega)
        (fun a ha => by have := hm a ha; omega)
  | loopX lim g ih =>
    intro m A d hw hR hm; simp only [need] at hR
    refine ⟨Xp.wf_comp lim d (by omega), rg_ne (by omega) (by omega), rg_ne (by omega) (by omega),
      rg_ne (by omega) (by omega), ?_, ?_, noX_comp g m A (d + 3) hw.1,
      ih m A (d + 3) hw.2 (by omega) (fun a ha => by have := hm a ha; omega)⟩
    · exact wr_false (by omega) (by omega) (fun a ha => by have := hm a ha; omega)
        (fun a ha => by have := hm a ha; omega)
    · exact wr_false (by omega) (by omega) (fun a ha => by have := hm a ha; omega)
        (fun a ha => by have := hm a ha; omega)
  | len g ih =>
    intro m A d hw hR hm; simp only [need] at hR
    exact ⟨trivial, ih m A (d + 1) hw (by omega) (fun a ha => by have := hm a ha; omega)⟩
  | log e g ih =>
    intro m A d hw hR hm; simp only [need] at hR
    have n0 : rg R (d + 3) ≠ rg R d := rg_ne (by omega) (by omega)
    have n2 : rg R (d + 3) ≠ rg R (d + 2) := rg_ne (by omega) (by omega)
    have n1 : rg R (d + 3) ≠ rg R (d + 1) := rg_ne (by omega) (by omega)
    have m0 : rg R (d + 1) ≠ rg R d := rg_ne (by omega) (by omega)
    have m2 : rg R (d + 1) ≠ rg R (d + 2) := rg_ne (by omega) (by omega)
    refine ⟨Xp.wf_comp e d (by omega), ⟨trivial, trivial, trivial, n1, ?_, ?_, ⟨trivial,
      trivial, trivial⟩⟩, ih m A (d + 1) hw (by omega) (fun a ha => by have := hm a ha; omega)⟩
    · simp [Stm.wr, n0, n2]
    · simp [Stm.wr, m0, m2]
  | count g h ihg ihh =>
    intro m A d hw hR hm; simp only [need] at hR
    exact ⟨trivial, ihg (some d) (d :: A) (d + 1) hw.1 (by omega) (fun a ha => by cases ha; omega),
      ihh m A (d + 1) hw.2 (by omega) (fun a ha => by have := hm a ha; omega)⟩

lemma depth_comp (g : Gn) : ∀ (m : Option ℕ) (A : List ℕ) (d : ℕ),
    (comp R m A d g).depth ≤ 3 := by
  induction g with
  | skip => intro m A d; simp [comp, Stm.depth]
  | emit e =>
    intro m A d
    cases m with
    | none =>
      have := Xp.depth_comp (R := R) (d := d) (A := A) e d
      simp only [comp, Stm.depth, Ex.depth]; omega
    | some a => simp [comp, incr, Stm.depth, Ex.depth]
  | seq g h ihg ihh =>
    intro m A d; have := ihg m A d; have := ihh m A d; simp only [comp, Stm.depth]; omega
  | ite c g h ihg ihh =>
    intro m A d; have := ihg m A d; have := ihh m A d
    have := Xp.depth_comp (R := R) (d := d) (A := A) c d
    simp only [comp, Stm.depth, Ex.depth]; omega
  | bind e g ih =>
    intro m A d; have := ih m A (d + 1); have := Xp.depth_comp (R := R) (d := d) (A := A) e d
    simp only [comp, Stm.depth]; omega
  | loop lim g ih =>
    intro m A d; have := ih m A (d + 2)
    have := Xp.depth_comp (R := R) (d := d) (A := A) lim d
    simp only [comp, Stm.depth]; omega
  | loopX lim g ih =>
    intro m A d; have := ih m A (d + 3)
    have := Xp.depth_comp (R := R) (d := d) (A := A) lim d
    simp only [comp, Stm.depth]; omega
  | len g ih => intro m A d; have := ih m A (d + 1); simp only [comp, Stm.depth]; omega
  | log e g ih =>
    intro m A d; have := ih m A (d + 1); have := Xp.depth_comp (R := R) (d := d) (A := A) e d
    simp only [comp, logS, Stm.depth, Ex.depth]; omega
  | count g h ihg ihh =>
    intro m A d; have := ihg (some d) (d :: A) (d + 1); have := ihh m A (d + 1)
    simp only [comp, Stm.depth, Ex.depth]; omega

/-- The machine of a generator. -/
noncomputable def machine (R : ℕ) (g : Gn) : Machine :=
  ((comp R none [] 0 g).code (R + 1) 3).machine

/-- **Machines of generators.** -/
theorem computesWithin {g : Gn} {B : ℕ} (hw : 2 ≤ w) (hB : 2 * B ≤ 2 ^ w) (hR : g.need ≤ R)
    (hwf : g.WFX) (hf : g.Fits x B [])
    (hlen : x.length ≤ (encodeNats (g.out x [])).length) :
    ComputesWithin (machine R g) x (encodeNats (g.out x []))
      (κ w * g.cost x [] + 20 * (encodeNats (g.out x [])).length + 4) := by
  have P : Pre R none [] 0 [] (fun _ => 0) :=
    ⟨rfl, fun i hi => by simp at hi, fun a ha => (by cases ha), fun i hi => by omega⟩
  obtain ⟨G, -⟩ := spec (x := x) hB g none [] 0 [] (fun _ => 0) P (by omega) hf
    (fun a ha => by cases ha)
  exact Stm.computesWithin hw (wf_comp g none [] 0 hwf (by omega) (fun a ha => by cases ha))
    (depth_comp g none [] 0) G hlen

end Gn

end Lax119563Proofs.Reduction

end Reduction_GMachine

/-! ### Formerly `Lax119563Proofs.Reduction.GTools` -/

section Reduction_GTools

/-!
# A toolkit for generators

* derived expressions: `Xp.eq`, `Xp.not`, `Xp.and`, `Xp.or` (on `0/1`), `Xp.mulC` (by a
  constant), `Xp.pow2`, with their values;
* derived generators: `Gn.seqL` (a static list) and `Gn.when`, with their outputs.
-/

namespace Lax119563Proofs.Reduction

namespace Xp

/-- `1` if `a = b`, else `0`. -/
def eq (a b : Xp) : Xp := lt (add (lt a b) (lt b a)) (const 1)
/-- `1` if `a = 0`, else `0`. -/
def not (a : Xp) : Xp := lt a (const 1)
/-- `1` if `a, b ≠ 0` (for `a, b ≤ 1`). -/
def and (a b : Xp) : Xp := lt (const 1) (add a b)
/-- `1` if `a ≠ 0` or `b ≠ 0`. -/
def or (a b : Xp) : Xp := lt (const 0) (add a b)
/-- `c * a`. -/
def mulC : ℕ → Xp → Xp
  | 0, _ => const 0
  | c + 1, a => add (mulC c a) a
/-- `2 ^ k`. -/
def pow2 (k : Xp) : Xp := shl (const 1) k

variable {ρ : List ℕ}

@[simp] lemma eval_eq (a b : Xp) : (eq a b).eval ρ = if a.eval ρ = b.eval ρ then 1 else 0 := by
  simp only [eq, eval]; split_ifs <;> omega
@[simp] lemma eval_not (a : Xp) : (not a).eval ρ = if a.eval ρ = 0 then 1 else 0 := by
  simp only [Xp.not, eval]; by_cases h : a.eval ρ = 0 <;> simp [h]
@[simp] lemma eval_mulC (c : ℕ) (a : Xp) : (mulC c a).eval ρ = c * a.eval ρ := by
  induction c with
  | zero => simp [mulC, eval]
  | succ c ih => simp only [mulC, eval, ih]; ring
@[simp] lemma eval_pow2 (k : Xp) : (pow2 k).eval ρ = 2 ^ k.eval ρ := by simp [pow2, eval]
@[simp] lemma eval_const (c : ℕ) : (const c).eval ρ = c := rfl
lemma eval_eq_const (a : Xp) (c : ℕ) :
    (eq a (const c)).eval ρ = if a.eval ρ = c then 1 else 0 := by
  show (if (if a.eval ρ < c then 1 else 0) + (if c < a.eval ρ then 1 else 0) < 1 then 1 else 0)
    = _
  split_ifs <;> omega
lemma eval_and {a b : Xp} (ha : a.eval ρ ≤ 1) (hb : b.eval ρ ≤ 1) :
    (and a b).eval ρ = if a.eval ρ = 1 ∧ b.eval ρ = 1 then 1 else 0 := by
  show (if (1 : ℕ) < a.eval ρ + b.eval ρ then 1 else 0) = _
  split_ifs <;> omega
lemma eval_or (a b : Xp) :
    (or a b).eval ρ = if a.eval ρ ≠ 0 ∨ b.eval ρ ≠ 0 then 1 else 0 := by
  show (if (0 : ℕ) < a.eval ρ + b.eval ρ then 1 else 0) = _
  split_ifs <;> omega

end Xp

namespace Gn

variable {x : List Bool} {ρ : List ℕ}

/-- A static list of generators, in order. -/
def seqL : List Gn → Gn
  | [] => skip
  | g :: gs => seq g (seqL gs)

/-- `g` if `c ≠ 0`. -/
def when (c : Xp) (g : Gn) : Gn := ite c g skip

lemma out_seqL (gs : List Gn) : (seqL gs).out x ρ = gs.flatMap fun g => g.out x ρ := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [seqL, out, ih]

lemma out_when (c : Xp) (g : Gn) :
    (when c g).out x ρ = if c.eval ρ ≠ 0 then g.out x ρ else [] := rfl

lemma flatMap_range_ite {β : Type} (n v : ℕ) (F : ℕ → List β) :
    (List.range n).flatMap (fun i => if v = i then F i else []) =
      if v < n then F v else [] := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton]
    by_cases h1 : v < n
    · simp [h1, show v < n + 1 by omega, show v ≠ n by omega]
    · rw [if_neg h1, List.nil_append]
      by_cases h2 : v = n
      · subst h2; simp
      · simp [h2, show ¬ v < n + 1 by omega]

/-! ### Fits and costs of derived generators -/

variable {B : ℕ}

end Gn

end Lax119563Proofs.Reduction

end Reduction_GTools

/-! ### Formerly `Lax119563Proofs.Reduction.GEnum` -/

section Reduction_GEnum

/-!
# Generator combinators for enumerations

* `Xp.Bnd n e`: `e` reads only stack levels `< n`; then `e.eval (ρ ++ l) = e.eval ρ` for
  `ρ.length = n` (`Xp.eval_append`).
* `Xp.mul a b = mulB a b b` (exactly `a * b`, cost about the value of `b`).
* `Gn.bindL es g`: push the values of a list of expressions.
* `Gn.bindSub n a b g`: push `a - b` (truncated), by counting.
* `flatMap_range_mul`: enumerating `range (a * b)` as `b` blocks of `a`.
-/

namespace Lax119563Proofs.Reduction

namespace Xp

variable {ρ : List ℕ}

/-- The expression reads only the stack levels below `n`. -/
def Bnd (n : ℕ) : Xp → Prop
  | var i => i < n
  | const _ => True
  | add a b => a.Bnd n ∧ b.Bnd n
  | lt a b => a.Bnd n ∧ b.Bnd n
  | half a => a.Bnd n
  | odd a => a.Bnd n
  | mulB a b k => a.Bnd n ∧ b.Bnd n ∧ k.Bnd n
  | shl a k => a.Bnd n ∧ k.Bnd n
  | shr a k => a.Bnd n ∧ k.Bnd n
  | xorM a b k => a.Bnd n ∧ b.Bnd n ∧ k.Bnd n

lemma Bnd.mono {n n' : ℕ} (h : n ≤ n') {e : Xp} (he : e.Bnd n) : e.Bnd n' := by
  induction e with
  | var _ => exact lt_of_lt_of_le he h
  | const _ => trivial
  | add _ _ ia ib => exact ⟨ia he.1, ib he.2⟩
  | lt _ _ ia ib => exact ⟨ia he.1, ib he.2⟩
  | half _ ia => exact ia he
  | odd _ ia => exact ia he
  | mulB _ _ _ ia ib ik => exact ⟨ia he.1, ib he.2.1, ik he.2.2⟩
  | shl _ _ ia ik => exact ⟨ia he.1, ik he.2⟩
  | shr _ _ ia ik => exact ⟨ia he.1, ik he.2⟩
  | xorM _ _ _ ia ib ik => exact ⟨ia he.1, ib he.2.1, ik he.2.2⟩

lemma eval_append {n : ℕ} (hρ : ρ.length = n) (l : List ℕ) {e : Xp} (he : e.Bnd n) :
    e.eval (ρ ++ l) = e.eval ρ := by
  induction e with
  | var i =>
    simp only [eval]
    exact List.getD_append _ _ _ _ (by simp only [Bnd] at he; omega)
  | const _ => rfl
  | add _ _ ia ib => simp only [eval, ia he.1, ib he.2]
  | lt _ _ ia ib => simp only [eval, ia he.1, ib he.2]
  | half _ ia => simp only [eval, ia he]
  | odd _ ia => simp only [eval, ia he]
  | mulB _ _ _ ia ib ik => simp only [eval, ia he.1, ib he.2.1, ik he.2.2]
  | shl _ _ ia ik => simp only [eval, ia he.1, ik he.2]
  | shr _ _ ia ik => simp only [eval, ia he.1, ik he.2]
  | xorM _ _ _ ia ib ik => simp only [eval, ia he.1, ib he.2.1, ik he.2.2]

/-- Exact multiplication `a * b` (by `b` doubling steps of `mulB`). -/
def mul (a b : Xp) : Xp := mulB a b b

@[simp] lemma eval_mul (a b : Xp) : (mul a b).eval ρ = a.eval ρ * b.eval ρ := by
  simp only [mul, eval, Nat.mod_eq_of_lt (Nat.lt_two_pow_self)]

lemma bnd_mul {n : ℕ} {a b : Xp} (ha : a.Bnd n) (hb : b.Bnd n) : (mul a b).Bnd n :=
  ⟨ha, hb, hb⟩

@[simp] lemma eval_var (i : ℕ) : (var i).eval ρ = ρ.getD i 0 := rfl
@[simp] lemma eval_add (a b : Xp) : (add a b).eval ρ = a.eval ρ + b.eval ρ := rfl
@[simp] lemma eval_lt_eq (a b : Xp) : (lt a b).eval ρ = if a.eval ρ < b.eval ρ then 1 else 0 := rfl
@[simp] lemma eval_shl (a k : Xp) : (shl a k).eval ρ = a.eval ρ * 2 ^ k.eval ρ := rfl

lemma bnd_mulC {n : ℕ} {a : Xp} (ha : a.Bnd n) : ∀ c, (mulC c a).Bnd n
  | 0 => trivial
  | c + 1 => ⟨bnd_mulC ha c, ha⟩

end Xp

namespace Gn

variable {x : List Bool} {ρ : List ℕ}

/-- Push the values of `es` (each evaluated on the stack extended by the previous ones). -/
def bindL : List Xp → Gn → Gn
  | [], g => g
  | e :: es, g => bind e (bindL es g)

lemma out_bindL (g : Gn) :
    ∀ (es : List Xp) {ρ : List ℕ} {n : ℕ}, ρ.length = n → (∀ e ∈ es, e.Bnd n) →
      (bindL es g).out x ρ = g.out x (ρ ++ es.map fun e => e.eval ρ)
  | [], _, _, _, _ => by simp [bindL]
  | e :: es, ρ, n, hρ, h => by
    simp only [bindL, out, List.map_cons]
    have hρ' : (ρ ++ [e.eval ρ]).length = n + 1 := by simp [hρ]
    rw [out_bindL g es hρ' (fun e' he' => Xp.Bnd.mono (Nat.le_succ n) (h e' (by simp [he'])))]
    rw [List.append_assoc]
    congr 2
    simp only [List.singleton_append, List.cons.injEq, true_and]
    exact List.map_congr_left fun e' he' => Xp.eval_append hρ _ (h e' (by simp [he']))

/-- Push `a - b` (truncated), counting `k < a` with `b < k + 1`; `n` is the stack depth. -/
def bindSub (n : ℕ) (a b : Xp) (g : Gn) : Gn :=
  count (loop a (when (Xp.lt b (Xp.add (Xp.var (n + 2)) (Xp.const 1))) (emit (Xp.const 0)))) g

lemma length_flatMap_ge (A B : ℕ) :
    ((List.range A).flatMap fun k => if B < k + 1 then [0] else []).length = A - B := by
  induction A with
  | zero => simp
  | succ A ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp only [List.flatMap_singleton]
    split_ifs <;> simp <;> omega

lemma out_bindSub {n : ℕ} (hρ : ρ.length = n) {a b : Xp} (ha : a.Bnd n) (hb : b.Bnd n)
    (g : Gn) : (bindSub n a b g).out x ρ = g.out x (ρ ++ [a.eval ρ - b.eval ρ]) := by
  simp only [bindSub, out]
  congr 3
  have h1 : (ρ ++ [0]).length = n + 1 := by simp [hρ]
  rw [Xp.eval_append hρ _ ha]
  have : (List.range (a.eval ρ)).flatMap (fun k => (when (Xp.lt b (Xp.add (Xp.var (n + 2))
      (Xp.const 1))) (emit (Xp.const 0))).out x (ρ ++ [0] ++ [a.eval ρ, k])) =
      (List.range (a.eval ρ)).flatMap fun k => if b.eval ρ < k + 1 then [0] else [] := by
    refine List.flatMap_congr fun k _ => ?_
    rw [out_when]
    have e1 : b.eval (ρ ++ [0] ++ [a.eval ρ, k]) = b.eval ρ := by
      rw [List.append_assoc]; exact Xp.eval_append hρ _ hb
    have e2 : (ρ ++ [0] ++ [a.eval ρ, k]).getD (n + 2) 0 = k := by
      rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
      simp [hρ]
    show (if (if b.eval (ρ ++ [0] ++ [a.eval ρ, k]) <
        (ρ ++ [0] ++ [a.eval ρ, k]).getD (n + 2) 0 + 1 then 1 else 0) ≠ 0 then [0] else []) = _
    rw [e1, e2]
    split_ifs <;> simp_all
  rw [this, length_flatMap_ge]

/-! ## Enumerating a product range -/

lemma flatMap_range_mul {β : Type} (a b : ℕ) (F : ℕ → List β) :
    (List.range (a * b)).flatMap F =
      (List.range b).flatMap fun q => (List.range a).flatMap fun r => F (r + a * q) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, List.range_add, List.flatMap_append, ih, List.range_succ,
      List.flatMap_append, List.flatMap_singleton, List.flatMap_map]
    congr 1
    refine List.flatMap_congr fun r _ => ?_
    rw [Nat.add_comm (a * b) r]

end Gn

end Lax119563Proofs.Reduction

end Reduction_GEnum

/-! ### Formerly `Lax119563Proofs.Reduction.FitsBasic` -/

section Reduction_FitsBasic

/-!
# Basic facts about `Fits` and `cost`

* `Xp.Fits.mono`, `Gn.Fits.mono`: fitting below `B` is monotone in `B`;
* `Gn.lt_of_mem_out`: every emitted value of a fitting generator is `< B`;
* `Gn.length_out_le_cost`: a generator emits at most `cost` values.
-/

namespace Lax119563Proofs.Reduction

namespace Xp

lemma Fits.mono {B B' : ℕ} (hB : B ≤ B') {ρ : List ℕ} (e : Xp) : e.Fits B ρ → e.Fits B' ρ := by
  induction e with
  | var _ => exact fun h => lt_of_lt_of_le h hB
  | const _ => exact fun h => lt_of_lt_of_le h hB
  | add _ _ ia ib => exact fun h => ⟨ia h.1, ib h.2.1, lt_of_lt_of_le h.2.2 hB⟩
  | lt _ _ ia ib => exact fun h => ⟨ia h.1, ib h.2⟩
  | half _ ia => exact ia
  | odd _ ia => exact ia
  | mulB _ _ _ ia ib ik => exact fun h => ⟨ia h.1, ib h.2.1, ik h.2.2.1, lt_of_lt_of_le h.2.2.2 hB⟩
  | shl _ _ ia ik => exact fun h => ⟨ia h.1, ik h.2.1, lt_of_lt_of_le h.2.2 hB⟩
  | shr _ _ ia ik => exact fun h => ⟨ia h.1, ik h.2⟩
  | xorM _ _ _ ia ib ik => exact fun h => ⟨ia h.1, ib h.2.1, ik h.2.2.1, lt_of_lt_of_le h.2.2.2 hB⟩

end Xp

namespace Gn

variable {x : List Bool}

lemma Fits.mono {B B' : ℕ} (hB : B ≤ B') (g : Gn) : ∀ {ρ : List ℕ}, g.Fits x B ρ →
    g.Fits x B' ρ := by
  induction g with
  | skip => intro _ _; trivial
  | emit e => intro _ h; exact Xp.Fits.mono hB _ h
  | seq g h ihg ihh => intro _ H; exact ⟨ihg H.1, ihh H.2⟩
  | ite c g h ihg ihh =>
    intro ρ H
    refine ⟨Xp.Fits.mono hB _ H.1, ?_⟩
    have H2 := H.2
    split_ifs at H2 ⊢
    · exact ihg H2
    · exact ihh H2
  | bind e g ih => intro _ H; exact ⟨Xp.Fits.mono hB _ H.1, ih H.2⟩
  | loop lim g ih => intro _ H; exact ⟨Xp.Fits.mono hB _ H.1, fun k hk => ih (H.2 k hk)⟩
  | loopX lim g ih => intro _ H; exact ⟨Xp.Fits.mono hB _ H.1, fun k hk => ih (H.2 k hk)⟩
  | len g ih => intro _ H; exact ⟨lt_of_lt_of_le H.1 hB, ih H.2⟩
  | log e g ih => intro _ H; exact ⟨Xp.Fits.mono hB _ H.1, ih H.2⟩
  | count g h ihg ihh => intro _ H; exact ⟨lt_of_lt_of_le H.1 hB, ihg H.2.1, ihh H.2.2⟩

lemma lt_of_mem_out {B : ℕ} (g : Gn) : ∀ {ρ : List ℕ}, g.Fits x B ρ →
    ∀ v ∈ g.out x ρ, v < B := by
  induction g with
  | skip => intro _ _ v hv; simp [out] at hv
  | emit e =>
    intro ρ h v hv
    simp only [out, List.mem_singleton] at hv
    subst hv; exact Xp.eval_lt h
  | seq g h ihg ihh =>
    intro ρ H v hv
    simp only [out, List.mem_append] at hv
    rcases hv with hv | hv
    · exact ihg H.1 v hv
    · exact ihh H.2 v hv
  | ite c g h ihg ihh =>
    intro ρ H v hv
    have H2 := H.2
    simp only [out] at hv
    split_ifs at H2 hv
    · exact ihg H2 v hv
    · exact ihh H2 v hv
  | bind e g ih => intro ρ H v hv; exact ih H.2 v hv
  | loop lim g ih =>
    intro ρ H v hv
    simp only [out, List.mem_flatMap, List.mem_range] at hv
    obtain ⟨k, hk, hv⟩ := hv
    exact ih (H.2 k hk) v hv
  | loopX lim g ih =>
    intro ρ H v hv
    simp only [out, List.mem_flatMap, List.mem_range] at hv
    obtain ⟨k, hk, hv⟩ := hv
    exact ih (H.2 k hk) v hv
  | len g ih => intro ρ H v hv; exact ih H.2 v hv
  | log e g ih => intro ρ H v hv; exact ih H.2 v hv
  | count g h ihg ihh => intro ρ H v hv; exact ihh H.2.2 v hv

lemma length_flatMap_range_le {β : Type} (L : ℕ) (f : ℕ → List β) (c : ℕ → ℕ)
    (h : ∀ k < L, (f k).length ≤ c k) :
    ((List.range L).flatMap f).length ≤ ∑ k ∈ Finset.range L, c k := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, Finset.sum_range_succ]
    have := ih fun k hk => h k (by omega)
    have := h L (by omega)
    simp only [List.flatMap_singleton]
    omega

lemma length_out_le_cost (g : Gn) : ∀ ρ : List ℕ, (g.out x ρ).length ≤ g.cost x ρ := by
  induction g with
  | skip => intro _; simp [out, cost]
  | emit e => intro _; simp [out, cost]
  | seq g h ihg ihh =>
    intro ρ; have := ihg ρ; have := ihh ρ; simp only [out, cost, List.length_append]; omega
  | ite c g h ihg ihh =>
    intro ρ; have := ihg ρ; have := ihh ρ
    simp only [out, cost]
    split_ifs <;> omega
  | bind e g ih => intro ρ; have := ih (ρ ++ [e.eval ρ]); simp only [out, cost]; omega
  | loop lim g ih =>
    intro ρ
    simp only [out, cost]
    have := length_flatMap_range_le (lim.eval ρ) (fun k => g.out x (ρ ++ [lim.eval ρ, k]))
      (fun k => g.cost x (ρ ++ [lim.eval ρ, k]) + 1) fun k _ => by
        have := ih (ρ ++ [lim.eval ρ, k]); omega
    omega
  | loopX lim g ih =>
    intro ρ
    simp only [out, cost]
    have := length_flatMap_range_le (lim.eval ρ)
      (fun k => g.out x (ρ ++ [lim.eval ρ, k, inBit x k]))
      (fun k => g.cost x (ρ ++ [lim.eval ρ, k, inBit x k]) + 1) fun k _ => by
        have := ih (ρ ++ [lim.eval ρ, k, inBit x k]); omega
    omega
  | len g ih => intro ρ; have := ih (ρ ++ [x.length]); simp only [out, cost]; omega
  | log e g ih =>
    intro ρ; have := ih (ρ ++ [Nat.log 2 (e.eval ρ)]); simp only [out, cost]; omega
  | count g h ihg ihh =>
    intro ρ; have := ihh (ρ ++ [(g.out x (ρ ++ [0])).length]); simp only [out, cost]; omega

end Gn

end Lax119563Proofs.Reduction

end Reduction_FitsBasic

/-! ### Formerly `Lax119563Proofs.Reduction.CostTy` -/

section Reduction_CostTy

/-!
# Growth classes of values and typed expressions

To bound the values and the costs of generators uniformly in the input, every value is
assigned a *growth class* `Ty` with respect to a pair of scales `ℓ = (l, L)` (`Sc`, `l ≤ L`; a
scale is coerced to `L`): `2^l` bounds the input length, `L` the linear quantities:
* `P e d`: values `≤ K · 2^(e l) · (L + 1)^d` (`P 0 1`: linear, `P 0 d`: polynomial in `L`,
  `P 1 0`: linear in `2^l`);
* `big`: values `≤ 2^(K (L + 1))`, where `K` is a constant depending on the syntax only.

`Ag K ℓ τs ρ`: the stack `ρ` agrees with the classes `τs` (with constant `K`).
`Xp.HasTy τs e τ`: for every constant of the stack there is a constant `K` such that the value
of `e` is in class `τ`, `e` fits below `2^(K (L + 1))` and costs at most `K (L + 1)`. The
loop-based operations `mulB, shl, shr, xorM` need a linear (`P 0 1`) iteration count.

Typing rules: `Xp.hasTy_var/const/add/addBig/lt/half/odd/mulB/mulBBig/shl/shr/xorM`, with
`HasTy.le` (subsumption), `HasTy.ctx` (smaller context classes) and `HasTy.weaken`
(appending levels the expression does not read).
-/

namespace Lax119563Proofs.Reduction

/-- A pair of scales `l ≤ L`: `2^l` bounds the input length and the values of the classes
`P 1 _`, `L` the linear quantities. A scale is coerced to `L`. -/
structure Sc where
  /-- The exponential scale. -/
  l : ℕ
  /-- The linear scale. -/
  L : ℕ
  le : l ≤ L

instance : CoeOut Sc ℕ := ⟨Sc.L⟩

/-- Growth classes. -/
inductive Ty
  /-- At most `K · 2^(e ℓ) · ((ℓ : ℕ) + 1)^d`. -/
  | P (e d : ℕ)
  /-- At most `2^(K ((ℓ : ℕ) + 1))`. -/
  | big

namespace Ty

/-- The bound of a class with constant `K` at scale `ℓ`. -/
def bnd : Ty → ℕ → Sc → ℕ
  | P e d, K, ℓ => K * 2 ^ (e * ℓ.l) * ((ℓ : ℕ) + 1) ^ d
  | big, K, ℓ => 2 ^ (K * ((ℓ : ℕ) + 1))

/-- Inclusion of classes. -/
def Le : Ty → Ty → Prop
  | P e d, P e' d' => e ≤ e' ∧ d ≤ d'
  | _, big => True
  | big, P _ _ => False

/-- The increase of the constant when passing to a larger class. -/
def lift : Ty → ℕ
  | P e d => e + d
  | big => 0

lemma Le.refl : ∀ τ : Ty, Le τ τ
  | P _ _ => ⟨le_rfl, le_rfl⟩
  | big => trivial

lemma le_big (τ : Ty) : Le τ big := by cases τ <;> trivial

lemma bnd_mono {K K' : ℕ} (h : K ≤ K') (ℓ : Sc) : ∀ τ : Ty, τ.bnd K ℓ ≤ τ.bnd K' ℓ
  | P e d => by
    simp only [bnd]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h)
  | big => Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ h)

lemma succ_le_two_pow (ℓ : ℕ) : ℓ + 1 ≤ 2 ^ ℓ := Nat.lt_two_pow_self

lemma pow_succ_le (ℓ d : ℕ) : ((ℓ : ℕ) + 1) ^ d ≤ 2 ^ (d * ℓ) := by
  rw [Nat.mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (succ_le_two_pow ℓ) d

lemma bnd_le_big (K : ℕ) (ℓ : Sc) : ∀ τ : Ty, τ.bnd K ℓ ≤ 2 ^ ((K + τ.lift) * ((ℓ : ℕ) + 1))
  | P e d => by
    simp only [bnd, lift]
    have h1 : K ≤ 2 ^ K := Nat.lt_two_pow_self.le
    have h3 := pow_succ_le ℓ d
    have h2 : 2 ^ (e * ℓ.l) ≤ 2 ^ (e * ℓ) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ ℓ.le)
    calc K * 2 ^ (e * ℓ.l) * (↑ℓ + 1) ^ d ≤ 2 ^ K * 2 ^ (e * ℓ) * 2 ^ (d * ℓ) :=
          Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
      _ = 2 ^ (K + e * ℓ + d * ℓ) := by rw [pow_add, pow_add]
      _ ≤ 2 ^ ((K + (e + d)) * ((ℓ : ℕ) + 1)) :=
          Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  | big => by simp [bnd, lift]

lemma bnd_lt_big (K : ℕ) (ℓ : Sc) (τ : Ty) : τ.bnd K ℓ < 2 ^ ((K + τ.lift + 1) * ((ℓ : ℕ) + 1)) :=
  lt_of_le_of_lt (bnd_le_big K ℓ τ) (Nat.pow_lt_pow_right (by norm_num) (by nlinarith))

lemma bnd_le_of_le {τ τ' : Ty} (h : Le τ τ') (K : ℕ) (ℓ : Sc) : τ.bnd K ℓ ≤ τ'.bnd (K + τ.lift) ℓ := by
  cases τ with
  | P e d =>
    cases τ' with
    | P e' d' =>
      simp only [bnd, lift]
      have h1 : 2 ^ (e * ℓ.l) ≤ 2 ^ (e' * ℓ.l) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ h.1)
      have h2 : ((ℓ : ℕ) + 1) ^ d ≤ ((ℓ : ℕ) + 1) ^ d' := Nat.pow_le_pow_right (by omega) h.2
      exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) h1) h2
    | big => exact bnd_le_big K ℓ _
  | big =>
    cases τ' with
    | P _ _ => exact h.elim
    | big => simp [bnd, lift]

lemma one_le_bnd {K : ℕ} (hK : 1 ≤ K) (ℓ : Sc) : ∀ τ : Ty, 1 ≤ τ.bnd K ℓ
  | P e d => by
    simp only [bnd]
    have h1 : 1 ≤ 2 ^ (e * ℓ.l) := Nat.one_le_two_pow
    have h2 : 1 ≤ ((ℓ : ℕ) + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    exact Nat.mul_le_mul (Nat.mul_le_mul hK h1) h2
  | big => Nat.one_le_two_pow

lemma bnd_P00 (K : ℕ) (ℓ : Sc) : (P 0 0).bnd K ℓ = K := by simp [bnd]

lemma bnd_mul (e d e' d' K K' : ℕ) (ℓ : Sc) :
    (P e d).bnd K ℓ * (P e' d').bnd K' ℓ = (P (e + e') (d + d')).bnd (K * K') ℓ := by
  simp only [bnd, Nat.add_mul, pow_add]; ring

lemma bnd_add (e d K K' : ℕ) (ℓ : Sc) :
    (P e d).bnd K ℓ + (P e d).bnd K' ℓ = (P e d).bnd (K + K') ℓ := by
  simp only [bnd]; ring

end Ty

open Ty

/-- The stack `ρ` agrees with the classes `τs`, with constant `K` at scale `ℓ`. -/
def Ag (K : ℕ) (ℓ : Sc) (τs : List Ty) (ρ : List ℕ) : Prop :=
  List.Forall₂ (fun v τ => v ≤ τ.bnd K ℓ) ρ τs

/-- Pointwise inclusion of classes. -/
def TysLe (τs τs' : List Ty) : Prop := List.Forall₂ Ty.Le τs τs'

/-- The sum of the lifts. -/
def liftL (τs : List Ty) : ℕ := (τs.map Ty.lift).sum

namespace Ag

variable {K K' : ℕ} {ℓ : Sc} {τs : List Ty} {ρ : List ℕ}

lemma mono (h : K ≤ K') (hA : Ag K ℓ τs ρ) : Ag K' ℓ τs ρ :=
  hA.imp fun _ τ hv => le_trans hv (Ty.bnd_mono h ℓ τ)

lemma length_eq (hA : Ag K ℓ τs ρ) : ρ.length = τs.length := List.Forall₂.length_eq hA

lemma getD (hA : Ag K ℓ τs ρ) (i : ℕ) : ρ.getD i 0 ≤ (τs.getD i (P 0 0)).bnd K ℓ := by
  induction hA generalizing i with
  | nil => simp
  | cons h _ ih =>
    cases i with
    | zero => simpa using h
    | succ i => simpa using ih i

lemma append {τs' : List Ty} {ρ' : List ℕ} (hA : Ag K ℓ τs ρ) (hA' : Ag K ℓ τs' ρ') :
    Ag K ℓ (τs ++ τs') (ρ ++ ρ') := List.rel_append hA hA'

lemma push {τ : Ty} {v : ℕ} (hA : Ag K ℓ τs ρ) (hv : v ≤ τ.bnd K ℓ) :
    Ag K ℓ (τs ++ [τ]) (ρ ++ [v]) := hA.append (List.Forall₂.cons hv List.Forall₂.nil)

lemma push2 {τ τ' : Ty} {v v' : ℕ} (hA : Ag K ℓ τs ρ) (hv : v ≤ τ.bnd K ℓ)
    (hv' : v' ≤ τ'.bnd K ℓ) : Ag K ℓ (τs ++ [τ, τ']) (ρ ++ [v, v']) :=
  hA.append (List.Forall₂.cons hv (List.Forall₂.cons hv' List.Forall₂.nil))

lemma push3 {τ τ' τ'' : Ty} {v v' v'' : ℕ} (hA : Ag K ℓ τs ρ) (hv : v ≤ τ.bnd K ℓ)
    (hv' : v' ≤ τ'.bnd K ℓ) (hv'' : v'' ≤ τ''.bnd K ℓ) :
    Ag K ℓ (τs ++ [τ, τ', τ'']) (ρ ++ [v, v', v'']) :=
  hA.append (List.Forall₂.cons hv (List.Forall₂.cons hv' (List.Forall₂.cons hv''
    List.Forall₂.nil)))

lemma split {τs' : List Ty} {ρ : List ℕ} (hA : Ag K ℓ (τs ++ τs') ρ) :
    Ag K ℓ τs (ρ.take τs.length) ∧ ρ = ρ.take τs.length ++ ρ.drop τs.length := by
  refine ⟨?_, (List.take_append_drop _ _).symm⟩
  induction τs generalizing ρ with
  | nil => exact List.Forall₂.nil
  | cons τ τs ih =>
    cases hA with
    | cons hv hr => exact List.Forall₂.cons hv (ih hr)

lemma of_le {τs' : List Ty} (h : TysLe τs τs') (hA : Ag K ℓ τs ρ) :
    Ag (K + liftL τs) ℓ τs' ρ := by
  induction hA generalizing τs' with
  | nil => cases h; exact List.Forall₂.nil
  | @cons v τ ρ τs hv _ ih =>
    cases h with
    | cons hτ hr =>
      refine List.Forall₂.cons ?_ ((ih hr).mono ?_)
      · refine le_trans hv (le_trans (Ty.bnd_le_of_le hτ K ℓ) (Ty.bnd_mono ?_ ℓ _))
        simp [liftL]
      · simp [liftL]

end Ag

lemma TysLe.refl : ∀ τs : List Ty, TysLe τs τs
  | [] => List.Forall₂.nil
  | τ :: τs => List.Forall₂.cons (Ty.Le.refl τ) (TysLe.refl τs)

lemma TysLe.append {τs τs' us us' : List Ty} (h : TysLe τs τs') (h' : TysLe us us') :
    TysLe (τs ++ us) (τs' ++ us') := List.rel_append h h'

/-! ## Expressions that ignore appended levels -/

namespace Xp

lemma fits_append {n : ℕ} {ρ : List ℕ} (hρ : ρ.length = n) (l : List ℕ) {B : ℕ} {e : Xp}
    (he : e.Bnd n) : e.Fits B (ρ ++ l) ↔ e.Fits B ρ := by
  induction e with
  | var i =>
    simp only [Fits]
    rw [List.getD_append _ _ _ _ (by simp only [Bnd] at he; omega)]
  | const _ => rfl
  | add a b ia ib =>
    simp only [Fits, ia he.1, ib he.2, eval_append hρ l he.1, eval_append hρ l he.2]
  | lt a b ia ib => simp only [Fits, ia he.1, ib he.2]
  | half a ia => exact ia he
  | odd a ia => exact ia he
  | mulB a b k ia ib ik =>
    simp only [Fits, ia he.1, ib he.2.1, ik he.2.2, eval_append hρ l he.1,
      eval_append hρ l he.2.2]
  | shl a k ia ik =>
    simp only [Fits, ia he.1, ik he.2, eval_append hρ l he.1, eval_append hρ l he.2]
  | shr a k ia ik => simp only [Fits, ia he.1, ik he.2]
  | xorM a b k ia ib ik =>
    simp only [Fits, ia he.1, ib he.2.1, ik he.2.2, eval_append hρ l he.2.2]

lemma cost_append {n : ℕ} {ρ : List ℕ} (hρ : ρ.length = n) (l : List ℕ) {e : Xp}
    (he : e.Bnd n) : e.cost (ρ ++ l) = e.cost ρ := by
  induction e with
  | var _ => rfl
  | const _ => rfl
  | add a b ia ib => simp only [cost, ia he.1, ib he.2]
  | lt a b ia ib => simp only [cost, ia he.1, ib he.2]
  | half a ia => simp only [cost, ia he]
  | odd a ia => simp only [cost, ia he]
  | mulB a b k ia ib ik =>
    simp only [cost, ia he.1, ib he.2.1, ik he.2.2, eval_append hρ l he.2.2]
  | shl a k ia ik => simp only [cost, ia he.1, ik he.2, eval_append hρ l he.2]
  | shr a k ia ik => simp only [cost, ia he.1, ik he.2, eval_append hρ l he.2]
  | xorM a b k ia ib ik =>
    simp only [cost, ia he.1, ib he.2.1, ik he.2.2, eval_append hρ l he.2.2]

/-! ## Typed expressions -/

/-- `e` has values in class `τ`, fits below `2^(K (ℓ+1))` and costs at most `K ((ℓ : ℕ) + 1)`. -/
def HasTy (τs : List Ty) (e : Xp) (τ : Ty) : Prop :=
  ∀ K₀, ∃ K, ∀ (ℓ : Sc) ρ, Ag K₀ ℓ τs ρ →
    e.eval ρ ≤ τ.bnd K ℓ ∧ e.Fits (2 ^ (K * ((ℓ : ℕ) + 1))) ρ ∧ e.cost ρ ≤ K * ((ℓ : ℕ) + 1)

variable {τs : List Ty}

lemma two_pow_mono {K K' ℓ : ℕ} (h : K ≤ K') : 2 ^ (K * ((ℓ : ℕ) + 1)) ≤ 2 ^ (K' * ((ℓ : ℕ) + 1)) :=
  Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ h)

lemma HasTy.le {e : Xp} {τ τ' : Ty} (h : HasTy τs e τ) (hτ : Ty.Le τ τ') : HasTy τs e τ' := by
  intro K₀
  obtain ⟨K, hK⟩ := h K₀
  refine ⟨K + τ.lift, fun ℓ ρ hA => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hK ℓ ρ hA
  exact ⟨le_trans h1 (Ty.bnd_le_of_le hτ K ℓ), Fits.mono (two_pow_mono (by omega)) _ h2,
    le_trans h3 (Nat.mul_le_mul_right _ (by omega))⟩

lemma HasTy.big {e : Xp} {τ : Ty} (h : HasTy τs e τ) : HasTy τs e .big := h.le (Ty.le_big τ)

lemma HasTy.weaken {e : Xp} {τ : Ty} (h : HasTy τs e τ) (hb : e.Bnd τs.length)
    (ts : List Ty) : HasTy (τs ++ ts) e τ := by
  intro K₀
  obtain ⟨K, hK⟩ := h K₀
  refine ⟨K, fun ℓ ρ hA => ?_⟩
  obtain ⟨hA1, hρ⟩ := hA.split
  have hl : (ρ.take τs.length).length = τs.length := hA1.length_eq
  rw [hρ, eval_append hl _ hb, fits_append hl _ hb, cost_append hl _ hb]
  exact hK ℓ _ hA1

lemma HasTy.weaken' {n : ℕ} {e : Xp} {τ : Ty} (h : HasTy τs e τ) (hn : τs.length = n)
    (hb : e.Bnd n) (ts : List Ty) : HasTy (τs ++ ts) e τ := h.weaken (hn ▸ hb) ts

lemma hasTy_var (i : ℕ) : HasTy τs (var i) (τs.getD i (P 0 0)) := by
  intro K₀
  refine ⟨K₀ + (τs.getD i (P 0 0)).lift + 1, fun ℓ ρ hA => ?_⟩
  have hv := hA.getD i
  refine ⟨le_trans hv (Ty.bnd_mono (by omega) ℓ _), ?_, ?_⟩
  · exact lt_of_le_of_lt hv (Ty.bnd_lt_big K₀ ℓ _)
  · simp only [cost]; nlinarith

lemma hasTy_var' {i : ℕ} {τ : Ty} (h : τs.getD i (P 0 0) = τ) : HasTy τs (var i) τ :=
  h ▸ hasTy_var i

lemma hasTy_const (c : ℕ) : HasTy τs (const c) (P 0 0) := by
  intro _
  refine ⟨c + 1, fun ℓ ρ _ => ⟨by simp [Ty.bnd, eval], ?_, by simp only [cost]; nlinarith⟩⟩
  show c < 2 ^ ((c + 1) * ((ℓ : ℕ) + 1))
  calc c < 2 ^ c := Nat.lt_two_pow_self
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

lemma two_pow_add_le (A B K ℓ : ℕ) (hA : A ≤ 2 ^ (K * ((ℓ : ℕ) + 1))) (hB : B ≤ 2 ^ (K * ((ℓ : ℕ) + 1))) :
    A + B < 2 ^ ((K + 2) * ((ℓ : ℕ) + 1)) := by
  have : 2 ^ (K * ((ℓ : ℕ) + 1)) * 2 ^ 2 ≤ 2 ^ ((K + 2) * ((ℓ : ℕ) + 1)) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have : 0 < 2 ^ (K * ((ℓ : ℕ) + 1)) := by positivity
  by_contra hc
  omega

lemma hasTy_add {a b : Xp} {e d : ℕ} (ha : HasTy τs a (P e d)) (hb : HasTy τs b (P e d)) :
    HasTy τs (add a b) (P e d) := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  obtain ⟨Kb, hKb⟩ := hb K₀
  refine ⟨Ka + Kb + e + d + 2, fun ℓ ρ hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  obtain ⟨b1, b2, b3⟩ := hKb ℓ ρ hA
  have hs : a.eval ρ + b.eval ρ ≤ (P e d).bnd (Ka + Kb) ℓ := by
    rw [← Ty.bnd_add]; omega
  refine ⟨?_, ⟨Fits.mono (two_pow_mono (by omega)) _ a2, Fits.mono (two_pow_mono (by omega)) _ b2,
    ?_⟩, ?_⟩
  · exact le_trans hs (Ty.bnd_mono (by omega) ℓ _)
  · refine lt_of_le_of_lt hs (lt_of_lt_of_le (Ty.bnd_lt_big _ ℓ _) (two_pow_mono ?_))
    simp [Ty.lift]; omega
  · simp only [cost]; nlinarith

lemma hasTy_addBig {a b : Xp} {τa τb : Ty} (ha : HasTy τs a τa) (hb : HasTy τs b τb) :
    HasTy τs (add a b) .big := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha.big K₀
  obtain ⟨Kb, hKb⟩ := hb.big K₀
  refine ⟨Ka + Kb + 3, fun ℓ ρ hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  obtain ⟨b1, b2, b3⟩ := hKb ℓ ρ hA
  have a1' : a.eval ρ ≤ 2 ^ ((Ka + Kb) * ((ℓ : ℕ) + 1)) := le_trans a1 (two_pow_mono (by omega))
  have b1' : b.eval ρ ≤ 2 ^ ((Ka + Kb) * ((ℓ : ℕ) + 1)) := le_trans b1 (two_pow_mono (by omega))
  have hs := two_pow_add_le _ _ _ ℓ a1' b1'
  refine ⟨le_trans hs.le (two_pow_mono (by omega)), ⟨Fits.mono (two_pow_mono (by omega)) _ a2,
    Fits.mono (two_pow_mono (by omega)) _ b2, lt_of_lt_of_le hs (two_pow_mono (by omega))⟩, ?_⟩
  simp only [cost]; nlinarith

lemma hasTy_lt {a b : Xp} {τa τb : Ty} (ha : HasTy τs a τa) (hb : HasTy τs b τb) :
    HasTy τs (lt a b) (P 0 0) := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  obtain ⟨Kb, hKb⟩ := hb K₀
  refine ⟨Ka + Kb + 2, fun ℓ ρ hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  obtain ⟨b1, b2, b3⟩ := hKb ℓ ρ hA
  refine ⟨?_, ⟨Fits.mono (two_pow_mono (by omega)) _ a2, Fits.mono (two_pow_mono (by omega)) _ b2⟩,
    ?_⟩
  · rw [Ty.bnd_P00]; simp only [eval]; split_ifs <;> omega
  · simp only [cost]; nlinarith

lemma hasTy_odd {a : Xp} {τ : Ty} (ha : HasTy τs a τ) : HasTy τs (odd a) (P 0 0) := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  refine ⟨Ka + 1, fun ℓ ρ hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  refine ⟨?_, Fits.mono (two_pow_mono (by omega)) a a2, ?_⟩
  · rw [Ty.bnd_P00]; simp only [eval]; have := Nat.mod_lt (a.eval ρ) (show 2 > 0 by omega); omega
  · simp only [cost]; nlinarith

/-- A linear iteration count: `2^k` is `big`. -/
lemma two_pow_lin {k K : ℕ} {ℓ : Sc} (hk : k ≤ (P 0 1).bnd K ℓ) : 2 ^ k ≤ 2 ^ (K * ((ℓ : ℕ) + 1)) :=
  Nat.pow_le_pow_right (by norm_num) (by simpa [Ty.bnd] using hk)

lemma lin_le {k K : ℕ} {ℓ : Sc} (hk : k ≤ (P 0 1).bnd K ℓ) : k ≤ K * ((ℓ : ℕ) + 1) := by
  simpa [Ty.bnd] using hk

lemma mul_two_pow_lt {a k Ka Kk : ℕ} {ℓ : Sc} {τ : Ty} (ha : a ≤ τ.bnd Ka ℓ)
    (hk : k ≤ (P 0 1).bnd Kk ℓ) : a * 2 ^ k < 2 ^ ((Ka + τ.lift + Kk + 1) * ((ℓ : ℕ) + 1)) := by
  have h1 := le_trans ha (Ty.bnd_le_big Ka ℓ τ)
  have h2 := two_pow_lin hk
  calc a * 2 ^ k ≤ 2 ^ ((Ka + τ.lift) * ((ℓ : ℕ) + 1)) * 2 ^ (Kk * ((ℓ : ℕ) + 1)) := Nat.mul_le_mul h1 h2
    _ = 2 ^ ((Ka + τ.lift + Kk) * ((ℓ : ℕ) + 1)) := by rw [← pow_add]; ring_nf
    _ < _ := Nat.pow_lt_pow_right (by norm_num) (by nlinarith)

lemma hasTy_mulB {a b k : Xp} {e d e' d' : ℕ} (ha : HasTy τs a (P e d))
    (hb : HasTy τs b (P e' d')) (hk : HasTy τs k (P 0 1)) :
    HasTy τs (mulB a b k) (P (e + e') (d + d')) := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  obtain ⟨Kb, hKb⟩ := hb K₀
  obtain ⟨Kk, hKk⟩ := hk K₀
  refine ⟨Ka * Kb + Ka + Kb + 2 * Kk + e + d + 3, fun ℓ ρ hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  obtain ⟨b1, b2, b3⟩ := hKb ℓ ρ hA
  obtain ⟨k1, k2, k3⟩ := hKk ℓ ρ hA
  refine ⟨?_, ⟨Fits.mono (two_pow_mono (by omega)) _ a2, Fits.mono (two_pow_mono (by omega)) _ b2,
    Fits.mono (two_pow_mono (by omega)) _ k2, ?_⟩, ?_⟩
  · simp only [eval]
    calc a.eval ρ * (b.eval ρ % 2 ^ k.eval ρ) ≤ (P e d).bnd Ka ℓ * (P e' d').bnd Kb ℓ :=
          Nat.mul_le_mul a1 (le_trans (Nat.mod_le _ _) b1)
      _ = _ := Ty.bnd_mul ..
      _ ≤ _ := Ty.bnd_mono (by nlinarith) ℓ _
  · exact lt_of_lt_of_le (mul_two_pow_lt a1 k1) (two_pow_mono (by simp [Ty.lift]; omega))
  · have := lin_le k1
    have key : (Ka + Kb + 2 * Kk + 2) * ((ℓ : ℕ) + 1) ≤
        (Ka * Kb + Ka + Kb + 2 * Kk + e + d + 3) * ((ℓ : ℕ) + 1) := Nat.mul_le_mul_right _ (by omega)
    simp only [cost]; nlinarith

lemma hasTy_mulBBig {a b k : Xp} {τa τb : Ty} (ha : HasTy τs a τa) (hb : HasTy τs b τb)
    (hk : HasTy τs k (P 0 1)) : HasTy τs (mulB a b k) .big := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  obtain ⟨Kb, hKb⟩ := hb K₀
  obtain ⟨Kk, hKk⟩ := hk K₀
  refine ⟨Ka + τa.lift + Kb + 2 * Kk + 3, fun ℓ ρ hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  obtain ⟨b1, b2, b3⟩ := hKb ℓ ρ hA
  obtain ⟨k1, k2, k3⟩ := hKk ℓ ρ hA
  have hm := mul_two_pow_lt a1 k1
  have hv : (mulB a b k).eval ρ ≤ a.eval ρ * 2 ^ k.eval ρ := by
    simp only [eval]
    exact Nat.mul_le_mul_left _ (Nat.mod_lt _ (by positivity)).le
  refine ⟨le_trans hv (le_trans hm.le (two_pow_mono (by omega))),
    ⟨Fits.mono (two_pow_mono (by omega)) _ a2, Fits.mono (two_pow_mono (by omega)) _ b2,
    Fits.mono (two_pow_mono (by omega)) _ k2, lt_of_lt_of_le hm (two_pow_mono (by omega))⟩, ?_⟩
  have := lin_le k1
  have key : (Ka + Kb + 2 * Kk + 2) * ((ℓ : ℕ) + 1) ≤
      (Ka + τa.lift + Kb + 2 * Kk + 3) * ((ℓ : ℕ) + 1) := Nat.mul_le_mul_right _ (by omega)
  simp only [cost]; nlinarith

lemma hasTy_shl {a k : Xp} {τ : Ty} (ha : HasTy τs a τ) (hk : HasTy τs k (P 0 1)) :
    HasTy τs (shl a k) .big := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  obtain ⟨Kk, hKk⟩ := hk K₀
  refine ⟨Ka + τ.lift + 2 * Kk + 3, fun ℓ ρ hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  obtain ⟨k1, k2, k3⟩ := hKk ℓ ρ hA
  have hm := mul_two_pow_lt a1 k1
  refine ⟨le_trans hm.le (two_pow_mono (by omega)),
    ⟨Fits.mono (two_pow_mono (by omega)) _ a2, Fits.mono (two_pow_mono (by omega)) _ k2,
      lt_of_lt_of_le hm (two_pow_mono (by omega))⟩, ?_⟩
  have := lin_le k1
  have key : (Ka + 2 * Kk + 2) * ((ℓ : ℕ) + 1) ≤
      (Ka + τ.lift + 2 * Kk + 3) * ((ℓ : ℕ) + 1) := Nat.mul_le_mul_right _ (by omega)
  simp only [cost]; nlinarith

lemma hasTy_shr {a k : Xp} {τ : Ty} (ha : HasTy τs a τ) (hk : HasTy τs k (P 0 1)) :
    HasTy τs (shr a k) τ := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  obtain ⟨Kk, hKk⟩ := hk K₀
  refine ⟨Ka + 2 * Kk + 3, fun ℓ ρ hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  obtain ⟨k1, k2, k3⟩ := hKk ℓ ρ hA
  refine ⟨?_, ⟨Fits.mono (two_pow_mono (by omega)) _ a2, Fits.mono (two_pow_mono (by omega)) _ k2⟩,
    ?_⟩
  · simp only [eval]
    exact le_trans (Nat.div_le_self _ _) (le_trans a1 (Ty.bnd_mono (by omega) ℓ _))
  · have := lin_le k1
    have key : (Ka + 2 * Kk + 2) * ((ℓ : ℕ) + 1) ≤
        (Ka + 2 * Kk + 3) * ((ℓ : ℕ) + 1) := Nat.mul_le_mul_right _ (by omega)
    simp only [cost]; nlinarith

lemma hasTy_xorM {a b k : Xp} {τa τb : Ty} (ha : HasTy τs a τa) (hb : HasTy τs b τb)
    (hk : HasTy τs k (P 0 1)) : HasTy τs (xorM a b k) .big := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  obtain ⟨Kb, hKb⟩ := hb K₀
  obtain ⟨Kk, hKk⟩ := hk K₀
  refine ⟨Ka + Kb + 2 * Kk + 4, fun ℓ ρ hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  obtain ⟨b1, b2, b3⟩ := hKb ℓ ρ hA
  obtain ⟨k1, k2, k3⟩ := hKk ℓ ρ hA
  have h2 := two_pow_lin k1
  have h2' : 2 ^ k.eval ρ < 2 ^ ((Ka + Kb + 2 * Kk + 4) * ((ℓ : ℕ) + 1)) :=
    lt_of_le_of_lt h2 (Nat.pow_lt_pow_right (by norm_num) (by nlinarith))
  refine ⟨?_, ⟨Fits.mono (two_pow_mono (by omega)) _ a2, Fits.mono (two_pow_mono (by omega)) _ b2,
    Fits.mono (two_pow_mono (by omega)) _ k2, h2'⟩, ?_⟩
  · simp only [eval, Ty.bnd]
    exact le_trans (Nat.mod_lt _ (by positivity)).le h2'.le
  · have := lin_le k1
    have key : (Ka + Kb + 2 * Kk + 3) * ((ℓ : ℕ) + 1) ≤
        (Ka + Kb + 2 * Kk + 4) * ((ℓ : ℕ) + 1) := Nat.mul_le_mul_right _ (by omega)
    simp only [cost]; nlinarith

/-! ### Derived expressions -/

lemma hasTy_eq {a b : Xp} {τa τb : Ty} (ha : HasTy τs a τa) (hb : HasTy τs b τb) :
    HasTy τs (Xp.eq a b) (P 0 0) :=
  hasTy_lt (hasTy_add (hasTy_lt ha hb) (hasTy_lt hb ha)) (hasTy_const 1)

lemma hasTy_not {a : Xp} {τ : Ty} (ha : HasTy τs a τ) : HasTy τs (Xp.not a) (P 0 0) :=
  hasTy_lt ha (hasTy_const 1)

lemma hasTy_and {a b : Xp} {τa τb : Ty} (ha : HasTy τs a τa) (hb : HasTy τs b τb) :
    HasTy τs (Xp.and a b) (P 0 0) := hasTy_lt (hasTy_const 1) (hasTy_addBig ha hb)

lemma hasTy_or {a b : Xp} {τa τb : Ty} (ha : HasTy τs a τa) (hb : HasTy τs b τb) :
    HasTy τs (Xp.or a b) (P 0 0) := hasTy_lt (hasTy_const 0) (hasTy_addBig ha hb)

lemma hasTy_mulC {a : Xp} {e d : ℕ} (ha : HasTy τs a (P e d)) :
    ∀ c, HasTy τs (mulC c a) (P e d)
  | 0 => (hasTy_const 0).le ⟨Nat.zero_le _, Nat.zero_le _⟩
  | c + 1 => hasTy_add (hasTy_mulC ha c) ha

lemma hasTy_mul {a b : Xp} {e d d' : ℕ} (ha : HasTy τs a (P e d)) (hb : HasTy τs b (P 0 d'))
    (hb1 : HasTy τs b (P 0 1)) : HasTy τs (mul a b) (P e (d + d')) := by
  have := hasTy_mulB ha hb hb1
  simpa [mul] using this

lemma hasTy_pow2 {k : Xp} (hk : HasTy τs k (P 0 1)) : HasTy τs (pow2 k) .big :=
  hasTy_shl (hasTy_const 1) hk

end Xp

end Lax119563Proofs.Reduction

end Reduction_CostTy

/-! ### Formerly `Lax119563Proofs.Reduction.CostGn` -/

section Reduction_CostGn

/-!
# Generators with fits and cost bounds

`Gn.HasCost τs g e d`: on every stack agreeing with the classes `τs` (with any constant), and
every input with `|x| ≤ 2^ℓ`, the generator fits below `2^(K ((ℓ : ℕ) + 1))` and costs at most
`K · 2^(e ℓ) · ((ℓ : ℕ) + 1)^(d + 1)`, for a constant `K` depending only on the constant of the stack.
`Gn.HasLen τs g τ`: the output has length in class `τ` (used for the value pushed by `count`).

Rules for every constructor (`hasCost_skip/emit/seq/ite/bind/loop/loopX/len/log/count`), with
`HasCost.mono` (larger exponents) and `HasCost.ctx` (smaller context classes), and the derived
generators `seqL`, `when`, `bindL`, `bindSub`. The cost exponents add up along
nested loops: a loop over a linear range (`P 0 1`) adds `1` to `d`, a loop over a range linear in
`|x|` (`P 1 0`) adds `1` to `e`.
-/

namespace Lax119563Proofs.Reduction

open Ty Xp

namespace Ty

lemma bnd_P_mono {e e' d d' : ℕ} (he : e ≤ e') (hd : d ≤ d') (K : ℕ) (ℓ : Sc) :
    (P e d).bnd K ℓ ≤ (P e' d').bnd K ℓ := by
  simp only [bnd]
  have h1 : 2 ^ (e * ℓ.l) ≤ 2 ^ (e' * ℓ.l) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ he)
  have h2 : ((ℓ : ℕ) + 1) ^ d ≤ ((ℓ : ℕ) + 1) ^ d' := Nat.pow_le_pow_right (by omega) hd
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2

lemma lin_le_bnd (e d K : ℕ) (ℓ : Sc) : K * ((ℓ : ℕ) + 1) ≤ (P e (d + 1)).bnd K ℓ := by
  have := bnd_P_mono (Nat.zero_le e) (show 1 ≤ d + 1 by omega) K ℓ
  simpa [bnd] using this

lemma two_pow_le_bnd {e : ℕ} (he : 1 ≤ e) (d : ℕ) (ℓ : Sc) : 2 ^ ℓ.l ≤ (P e d).bnd 1 ℓ := by
  have := bnd_P_mono he (Nat.zero_le d) 1 ℓ
  simpa [bnd] using this

end Ty

namespace Gn

/-- Fits below `2^(K (ℓ+1))` with cost `≤ K 2^(e ℓ) (ℓ+1)^(d+1)`. -/
def HasCost (τs : List Ty) (g : Gn) (e d : ℕ) : Prop :=
  ∀ K₀, ∃ K, ∀ (ℓ : Sc) (x : List Bool) ρ, x.length ≤ 2 ^ ℓ.l → Ag K₀ ℓ τs ρ →
    g.Fits x (2 ^ (K * ((ℓ : ℕ) + 1))) ρ ∧ g.cost x ρ ≤ (P e (d + 1)).bnd K ℓ

/-- The output has length in class `τ`. -/
def HasLen (τs : List Ty) (g : Gn) (τ : Ty) : Prop :=
  ∀ K₀, ∃ K, ∀ (ℓ : Sc) (x : List Bool) ρ, x.length ≤ 2 ^ ℓ.l → Ag K₀ ℓ τs ρ →
    (g.out x ρ).length ≤ τ.bnd K ℓ

variable {τs : List Ty}

lemma fits_up {x : List Bool} {g : Gn} {K K' ℓ : ℕ} {ρ : List ℕ} (h : K ≤ K')
    (hf : g.Fits x (2 ^ (K * ((ℓ : ℕ) + 1))) ρ) : g.Fits x (2 ^ (K' * ((ℓ : ℕ) + 1))) ρ :=
  Fits.mono (two_pow_mono h) g hf

lemma xfits_up {e : Xp} {K K' ℓ : ℕ} {ρ : List ℕ} (h : K ≤ K')
    (hf : e.Fits (2 ^ (K * ((ℓ : ℕ) + 1))) ρ) : e.Fits (2 ^ (K' * ((ℓ : ℕ) + 1))) ρ :=
  Xp.Fits.mono (two_pow_mono h) e hf

lemma HasCost.mono {g : Gn} {e d e' d' : ℕ} (h : HasCost τs g e d) (he : e ≤ e') (hd : d ≤ d') :
    HasCost τs g e' d' := by
  intro K₀
  obtain ⟨K, hK⟩ := h K₀
  exact ⟨K, fun ℓ x ρ hx hA => ⟨(hK ℓ x ρ hx hA).1,
    le_trans (hK ℓ x ρ hx hA).2 (Ty.bnd_P_mono he (by omega) K ℓ)⟩⟩

lemma HasCost.ctx {τs' : List Ty} {g : Gn} {e d : ℕ} (hle : TysLe τs τs')
    (h : HasCost τs' g e d) : HasCost τs g e d := by
  intro K₀
  obtain ⟨K, hK⟩ := h (K₀ + liftL τs)
  exact ⟨K, fun ℓ x ρ hx hA => hK ℓ x ρ hx (hA.of_le hle)⟩

lemma HasLen.le {g : Gn} {τ τ' : Ty} (h : HasLen τs g τ) (hτ : Ty.Le τ τ') : HasLen τs g τ' := by
  intro K₀
  obtain ⟨K, hK⟩ := h K₀
  exact ⟨K + τ.lift, fun ℓ x ρ hx hA => le_trans (hK ℓ x ρ hx hA) (Ty.bnd_le_of_le hτ K ℓ)⟩

lemma HasCost.len {g : Gn} {e d : ℕ} (h : HasCost τs g e d) : HasLen τs g (P e (d + 1)) := by
  intro K₀
  obtain ⟨K, hK⟩ := h K₀
  exact ⟨K, fun ℓ x ρ hx hA => le_trans (length_out_le_cost g ρ) (hK ℓ x ρ hx hA).2⟩

/-! ## Constructors -/

lemma hasCost_skip : HasCost τs skip 0 0 := by
  intro _
  refine ⟨1, fun ℓ x ρ _ _ => ⟨trivial, ?_⟩⟩
  simp only [cost]; exact Ty.one_le_bnd le_rfl ℓ _

lemma hasCost_emit {a : Xp} {τ : Ty} (ha : HasTy τs a τ) : HasCost τs (emit a) 0 0 := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  refine ⟨Ka + 1, fun ℓ x ρ _ hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  refine ⟨xfits_up (by omega) a2, ?_⟩
  have := Ty.lin_le_bnd 0 0 (Ka + 1) ℓ
  simp only [cost]; nlinarith

lemma hasCost_seq {g h : Gn} {e d : ℕ} (hg : HasCost τs g e d) (hh : HasCost τs h e d) :
    HasCost τs (seq g h) e d := by
  intro K₀
  obtain ⟨Kg, hKg⟩ := hg K₀
  obtain ⟨Kh, hKh⟩ := hh K₀
  refine ⟨Kg + Kh, fun ℓ x ρ hx hA => ?_⟩
  obtain ⟨g1, g2⟩ := hKg ℓ x ρ hx hA
  obtain ⟨h1, h2⟩ := hKh ℓ x ρ hx hA
  refine ⟨⟨fits_up (by omega) g1, fits_up (by omega) h1⟩, ?_⟩
  simp only [cost]; rw [← Ty.bnd_add]; omega

lemma hasCost_ite {c : Xp} {τ : Ty} {g h : Gn} {e d : ℕ} (hc : HasTy τs c τ)
    (hg : HasCost τs g e d) (hh : HasCost τs h e d) : HasCost τs (ite c g h) e d := by
  intro K₀
  obtain ⟨Kc, hKc⟩ := hc K₀
  obtain ⟨Kg, hKg⟩ := hg K₀
  obtain ⟨Kh, hKh⟩ := hh K₀
  refine ⟨Kc + 1 + Kg + Kh, fun ℓ x ρ hx hA => ?_⟩
  obtain ⟨c1, c2, c3⟩ := hKc ℓ ρ hA
  obtain ⟨g1, g2⟩ := hKg ℓ x ρ hx hA
  obtain ⟨h1, h2⟩ := hKh ℓ x ρ hx hA
  have hl := Ty.lin_le_bnd e d (Kc + 1) ℓ
  have e1 := Ty.bnd_add e (d + 1) (Kc + 1) Kg ℓ
  have e2 := Ty.bnd_add e (d + 1) (Kc + 1 + Kg) Kh ℓ
  refine ⟨⟨xfits_up (by omega) c2, ?_⟩, ?_⟩
  · split_ifs
    · exact fits_up (by omega) g1
    · exact fits_up (by omega) h1
  · simp only [cost]
    have : (if c.eval ρ ≠ 0 then g.cost x ρ else h.cost x ρ) ≤
        (P e (d + 1)).bnd Kg ℓ + (P e (d + 1)).bnd Kh ℓ := by split_ifs <;> omega
    nlinarith

lemma hasCost_bind {a : Xp} {τ : Ty} {g : Gn} {e d : ℕ} (ha : HasTy τs a τ)
    (hg : HasCost (τs ++ [τ]) g e d) : HasCost τs (bind a g) e d := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  obtain ⟨Kg, hKg⟩ := hg (K₀ + Ka)
  refine ⟨Ka + Kg, fun ℓ x ρ hx hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  have hA' : Ag (K₀ + Ka) ℓ (τs ++ [τ]) (ρ ++ [a.eval ρ]) :=
    (hA.mono (by omega)).push (le_trans a1 (Ty.bnd_mono (by omega) ℓ τ))
  obtain ⟨g1, g2⟩ := hKg ℓ x _ hx hA'
  refine ⟨⟨xfits_up (by omega) a2, fits_up (by omega) g1⟩, ?_⟩
  have hl := Ty.lin_le_bnd e d Ka ℓ
  have e1 := Ty.bnd_add e (d + 1) Ka Kg ℓ
  simp only [cost]; omega

lemma sum_range_le_mul {L T : ℕ} (c : ℕ → ℕ) (h : ∀ k < L, c k ≤ T) :
    ∑ k ∈ Finset.range L, (c k + 1) ≤ L * (T + 1) := by
  have : ∑ k ∈ Finset.range L, (c k + 1) ≤ ∑ k ∈ Finset.range L, (T + 1) :=
    Finset.sum_le_sum fun k hk => by have := h k (Finset.mem_range.mp hk); omega
  simpa using this

/-- The arithmetic of a loop. -/
lemma loop_arith {Kl Kg ℓ L c0 S X Y : ℕ} (hX : 1 ≤ X) (hY : ℓ + 1 ≤ Y) (hL : L ≤ Kl * X)
    (hc0 : c0 ≤ Kl * ((ℓ : ℕ) + 1)) (hS : S ≤ L * (Kg * Y + 1)) :
    c0 + 1 + S ≤ (Kl * Kg + 2 * Kl + 1) * (X * Y) := by
  have hY1 : 1 ≤ Y := by omega
  have h1 : c0 ≤ Kl * (X * Y) := le_trans hc0 (Nat.mul_le_mul_left _ (by nlinarith))
  have h2 : 1 ≤ X * Y := by nlinarith
  have h3 : S ≤ Kl * X * (Kg * Y + 1) := le_trans hS (Nat.mul_le_mul_right _ hL)
  have h4 : Kl * X * (Kg * Y + 1) ≤ Kl * Kg * (X * Y) + Kl * (X * Y) := by
    have : Kl * X ≤ Kl * (X * Y) := Nat.mul_le_mul_left _ (by nlinarith)
    nlinarith
  nlinarith

lemma bnd_split (e₀ d₀ e d K : ℕ) (ℓ : Sc) :
    (P (e₀ + e) (d₀ + d + 1)).bnd K ℓ =
      K * ((2 ^ (e₀ * ℓ.l) * ((ℓ : ℕ) + 1) ^ d₀) * (2 ^ (e * ℓ.l) * ((ℓ : ℕ) + 1) ^ (d + 1))) := by
  simp only [Ty.bnd, Nat.add_mul, pow_add]; ring

lemma one_le_X (e d : ℕ) (ℓ : Sc) : 1 ≤ 2 ^ (e * ℓ.l) * ((ℓ : ℕ) + 1) ^ d :=
  Nat.one_le_iff_ne_zero.mpr (by positivity)

lemma succ_le_Y (e d : ℕ) (ℓ : Sc) : ↑ℓ + 1 ≤ 2 ^ (e * ℓ.l) * ((ℓ : ℕ) + 1) ^ (d + 1) := by
  have := Ty.lin_le_bnd e d 1 ℓ
  simpa [Ty.bnd] using this

lemma hasCost_loop {lim : Xp} {g : Gn} {e₀ d₀ e d : ℕ} (hl : HasTy τs lim (P e₀ d₀))
    (hg : HasCost (τs ++ [P e₀ d₀, P e₀ d₀]) g e d) :
    HasCost τs (loop lim g) (e₀ + e) (d₀ + d) := by
  intro K₀
  obtain ⟨Kl, hKl⟩ := hl K₀
  obtain ⟨Kg, hKg⟩ := hg (K₀ + Kl)
  refine ⟨Kl * Kg + 2 * Kl + 1 + Kg, fun ℓ x ρ hx hA => ?_⟩
  obtain ⟨l1, l2, l3⟩ := hKl ℓ ρ hA
  have hb : ∀ k < lim.eval ρ, Ag (K₀ + Kl) ℓ (τs ++ [P e₀ d₀, P e₀ d₀]) (ρ ++ [lim.eval ρ, k]) :=
    fun k hk => (hA.mono (by omega)).push2 (le_trans l1 (Ty.bnd_mono (by omega) ℓ _))
      (le_trans (le_trans hk.le l1) (Ty.bnd_mono (by omega) ℓ _))
  refine ⟨⟨xfits_up (by omega) l2, fun k hk => fits_up (by omega) (hKg ℓ x _ hx (hb k hk)).1⟩, ?_⟩
  simp only [cost]
  rw [bnd_split]
  have hS := sum_range_le_mul (L := lim.eval ρ) (T := (P e (d + 1)).bnd Kg ℓ)
    (fun k => g.cost x (ρ ++ [lim.eval ρ, k])) fun k hk => (hKg ℓ x _ hx (hb k hk)).2
  have key := loop_arith (Kl := Kl) (Kg := Kg) (one_le_X e₀ d₀ ℓ) (succ_le_Y e d ℓ)
    (by simpa [Ty.bnd, Nat.mul_assoc] using l1) l3
    (le_trans hS (by simp [Ty.bnd, Nat.mul_assoc]))
  refine le_trans key (Nat.mul_le_mul_right _ (by omega))

lemma hasCost_loopX {lim : Xp} {g : Gn} {e₀ d₀ e d : ℕ} (hl : HasTy τs lim (P e₀ d₀))
    (hg : HasCost (τs ++ [P e₀ d₀, P e₀ d₀, P 0 0]) g e d) :
    HasCost τs (loopX lim g) (max 1 (e₀ + e)) (d₀ + d) := by
  intro K₀
  obtain ⟨Kl, hKl⟩ := hl K₀
  obtain ⟨Kg, hKg⟩ := hg (K₀ + Kl + 2)
  refine ⟨Kl * Kg + 2 * Kl + 3 + Kg, fun ℓ x ρ hx hA => ?_⟩
  obtain ⟨l1, l2, l3⟩ := hKl ℓ ρ hA
  have hb : ∀ k < lim.eval ρ, Ag (K₀ + Kl + 2) ℓ (τs ++ [P e₀ d₀, P e₀ d₀, P 0 0])
      (ρ ++ [lim.eval ρ, k, inBit x k]) :=
    fun k hk => (hA.mono (by omega)).push3 (le_trans l1 (Ty.bnd_mono (by omega) ℓ _))
      (le_trans (le_trans hk.le l1) (Ty.bnd_mono (by omega) ℓ _))
      (by rw [Ty.bnd_P00]; have := inBit_le x k; omega)
  refine ⟨⟨xfits_up (by omega) l2, fun k hk => fits_up (by omega) (hKg ℓ x _ hx (hb k hk)).1⟩, ?_⟩
  simp only [cost]
  have hS := sum_range_le_mul (L := lim.eval ρ) (T := (P e (d + 1)).bnd Kg ℓ)
    (fun k => g.cost x (ρ ++ [lim.eval ρ, k, inBit x k])) fun k hk => (hKg ℓ x _ hx (hb k hk)).2
  have key := loop_arith (Kl := Kl) (Kg := Kg) (one_le_X e₀ d₀ ℓ) (succ_le_Y e d ℓ)
    (by simpa [Ty.bnd, Nat.mul_assoc] using l1) l3
    (le_trans hS (by simp [Ty.bnd, Nat.mul_assoc]))
  rw [← bnd_split] at key
  have k1 := Ty.bnd_P_mono (le_max_right 1 (e₀ + e)) le_rfl (Kl * Kg + 2 * Kl + 1) ℓ
    (d := d₀ + d + 1)
  have k2 := Ty.two_pow_le_bnd (le_max_left 1 (e₀ + e)) (d₀ + d + 1) ℓ
  have k2' : (P (max 1 (e₀ + e)) (d₀ + d + 1)).bnd 1 ℓ + (P (max 1 (e₀ + e)) (d₀ + d + 1)).bnd 1 ℓ
      = (P (max 1 (e₀ + e)) (d₀ + d + 1)).bnd 2 ℓ := Ty.bnd_add ..
  have k2'' := Nat.one_le_two_pow (n := ℓ.l)
  have k3 := Ty.bnd_add (max 1 (e₀ + e)) (d₀ + d + 1) (Kl * Kg + 2 * Kl + 1) 2 ℓ
  have k4 := Ty.bnd_mono (show Kl * Kg + 2 * Kl + 1 + 2 ≤ Kl * Kg + 2 * Kl + 3 + Kg by omega) ℓ
    (P (max 1 (e₀ + e)) (d₀ + d + 1))
  omega

lemma log_le_lin {v K : ℕ} {ℓ : Sc} {τ : Ty} (hv : v ≤ τ.bnd K ℓ) :
    Nat.log 2 v ≤ (P 0 1).bnd (K + τ.lift) ℓ := by
  have h := le_trans hv (Ty.bnd_le_big K ℓ τ)
  calc Nat.log 2 v ≤ Nat.log 2 (2 ^ ((K + τ.lift) * ((ℓ : ℕ) + 1))) := Nat.log_mono_right h
    _ = _ := by rw [Nat.log_pow (by norm_num)]; simp [Ty.bnd]

lemma hasCost_log {a : Xp} {g : Gn} {e₀ d₀ e d : ℕ} (ha : HasTy τs a (P e₀ d₀))
    (hg : HasCost (τs ++ [P 0 1]) g e d) : HasCost τs (log a g) (max e₀ e) (max d₀ d) := by
  intro K₀
  obtain ⟨Ka, hKa⟩ := ha K₀
  obtain ⟨Kg, hKg⟩ := hg (K₀ + Ka + e₀ + d₀)
  refine ⟨2 * Ka + Kg + 2, fun ℓ x ρ hx hA => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hKa ℓ ρ hA
  have hA' : Ag (K₀ + Ka + e₀ + d₀) ℓ (τs ++ [P 0 1]) (ρ ++ [Nat.log 2 (a.eval ρ)]) :=
    (hA.mono (by omega)).push (le_trans (log_le_lin a1)
      (Ty.bnd_mono (by simp [Ty.lift]; omega) ℓ _))
  obtain ⟨g1, g2⟩ := hKg ℓ x _ hx hA'
  refine ⟨⟨xfits_up (by omega) a2, fits_up (by omega) g1⟩, ?_⟩
  simp only [cost]
  have k1 := Ty.bnd_P_mono (le_max_right e₀ e) (show d + 1 ≤ max d₀ d + 1 by omega) Kg ℓ
  have k2 := Ty.bnd_P_mono (le_max_left e₀ e) (show d₀ ≤ max d₀ d + 1 by omega) Ka ℓ
  have k3 := Ty.lin_le_bnd (max e₀ e) (max d₀ d) (Ka + 2) ℓ
  have k4 := Ty.bnd_add (max e₀ e) (max d₀ d + 1) Ka (Ka + 2) ℓ
  have k5 := Ty.bnd_add (max e₀ e) (max d₀ d + 1) (Ka + (Ka + 2)) Kg ℓ
  have k6 : 2 ≤ (Ka + 2) * ((ℓ : ℕ) + 1) := by nlinarith
  have k7 := Ty.bnd_mono (show Ka + (Ka + 2) + Kg ≤ 2 * Ka + Kg + 2 by omega) ℓ
    (P (max e₀ e) (max d₀ d + 1))
  nlinarith

lemma hasCost_count {g h : Gn} {τ : Ty} {e d : ℕ} (hg : HasCost (τs ++ [P 0 0]) g e d)
    (hl : HasLen (τs ++ [P 0 0]) g τ) (hh : HasCost (τs ++ [τ]) h e d) :
    HasCost τs (count g h) e d := by
  intro K₀
  obtain ⟨Kg, hKg⟩ := hg K₀
  obtain ⟨Kl, hKl⟩ := hl K₀
  obtain ⟨Kh, hKh⟩ := hh (K₀ + Kl)
  refine ⟨Kg + Kh + Kl + τ.lift + 2, fun ℓ x ρ hx hA => ?_⟩
  have hA0 : Ag K₀ ℓ (τs ++ [P 0 0]) (ρ ++ [0]) := hA.push (Nat.zero_le _)
  obtain ⟨g1, g2⟩ := hKg ℓ x _ hx hA0
  have l1 := hKl ℓ x _ hx hA0
  obtain ⟨h1, h2⟩ := hKh ℓ x _ hx ((hA.mono (by omega)).push
    (le_trans l1 (Ty.bnd_mono (by omega) ℓ τ)))
  refine ⟨⟨lt_of_le_of_lt l1 (lt_of_lt_of_le (Ty.bnd_lt_big Kl ℓ τ) (two_pow_mono (by omega))),
    fits_up (by omega) g1, fits_up (by omega) h1⟩, ?_⟩
  simp only [cost]
  have k1 := Ty.one_le_bnd (le_refl 1) ℓ (P e (d + 1))
  have k2 := Ty.bnd_add e (d + 1) Kg Kh ℓ
  have k3 := Ty.bnd_add e (d + 1) (Kg + Kh) 1 ℓ
  have k4 := Ty.bnd_mono (show Kg + Kh + 1 ≤ Kg + Kh + Kl + τ.lift + 2 by omega) ℓ (P e (d + 1))
  omega

/-! ## Output lengths -/

lemma hasLen_emit (a : Xp) : HasLen τs (emit a) (P 0 0) :=
  fun _ => ⟨1, fun _ _ _ _ _ => by simp [out, Ty.bnd]⟩

lemma hasLen_when (c : Xp) {g : Gn} {τ : Ty} (hg : HasLen τs g τ) : HasLen τs (when c g) τ := by
  intro K₀
  obtain ⟨K, hK⟩ := hg K₀
  refine ⟨K, fun ℓ x ρ hx hA => ?_⟩
  rw [out_when]
  split_ifs
  · exact hK ℓ x ρ hx hA
  · exact Nat.zero_le _

lemma hasLen_loop {lim : Xp} {g : Gn} {e₀ d₀ e d : ℕ} (hl : HasTy τs lim (P e₀ d₀))
    (hg : HasLen (τs ++ [P e₀ d₀, P e₀ d₀]) g (P e d)) :
    HasLen τs (loop lim g) (P (e₀ + e) (d₀ + d)) := by
  intro K₀
  obtain ⟨Kl, hKl⟩ := hl K₀
  obtain ⟨Kg, hKg⟩ := hg (K₀ + Kl)
  refine ⟨Kl * Kg, fun ℓ x ρ hx hA => ?_⟩
  obtain ⟨l1, -, -⟩ := hKl ℓ ρ hA
  have hb : ∀ k < lim.eval ρ, Ag (K₀ + Kl) ℓ (τs ++ [P e₀ d₀, P e₀ d₀]) (ρ ++ [lim.eval ρ, k]) :=
    fun k hk => (hA.mono (by omega)).push2 (le_trans l1 (Ty.bnd_mono (by omega) ℓ _))
      (le_trans (le_trans hk.le l1) (Ty.bnd_mono (by omega) ℓ _))
  simp only [out]
  have h1 := length_flatMap_range_le (lim.eval ρ) (fun k => g.out x (ρ ++ [lim.eval ρ, k]))
    (fun _ => (P e d).bnd Kg ℓ) fun k hk => hKg ℓ x _ hx (hb k hk)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at h1
  rw [← Ty.bnd_mul]
  exact le_trans h1 (Nat.mul_le_mul_right _ l1)

/-! ## Derived generators -/

lemma hasCost_seqL {e d : ℕ} : ∀ {gs : List Gn}, (∀ g ∈ gs, HasCost τs g e d) →
    HasCost τs (seqL gs) e d
  | [], _ => hasCost_skip.mono (Nat.zero_le _) (Nat.zero_le _)
  | g :: gs, h => hasCost_seq (h g (by simp)) (hasCost_seqL fun g' hg' => h g' (by simp [hg']))

lemma hasCost_when {c : Xp} {τ : Ty} {g : Gn} {e d : ℕ} (hc : HasTy τs c τ)
    (hg : HasCost τs g e d) : HasCost τs (when c g) e d :=
  hasCost_ite hc hg (hasCost_skip.mono (Nat.zero_le _) (Nat.zero_le _))

/-- Classes of a list of expressions, each typed in the context extended by the previous
ones. -/
def TyL : List Ty → List Xp → List Ty → Prop
  | _, [], [] => True
  | τs, a :: as, τ :: ts => HasTy τs a τ ∧ TyL (τs ++ [τ]) as ts
  | _, _, _ => False

lemma hasCost_bindL {g : Gn} {e d : ℕ} : ∀ {τs : List Ty} {as : List Xp} {ts : List Ty},
    TyL τs as ts → HasCost (τs ++ ts) g e d → HasCost τs (bindL as g) e d
  | _, [], [], _, hg => by simpa [bindL] using hg
  | τs, a :: as, τ :: ts, h, hg =>
    hasCost_bind h.1 (hasCost_bindL h.2 (by simpa using hg))
  | _, [], _ :: _, h, _ => h.elim
  | _, _ :: _, [], h, _ => h.elim

/-- `TyL` for expressions reading only the base context. -/
lemma tyL_of_forall₂ : ∀ {τs : List Ty} {as : List Xp} {ts : List Ty},
    List.Forall₂ (fun a τ => HasTy τs a τ ∧ a.Bnd τs.length) as ts → ∀ us : List Ty,
      TyL (τs ++ us) as ts
  | _, [], [], _, _ => trivial
  | τs, a :: as, τ :: ts, List.Forall₂.cons h hr, us =>
    ⟨h.1.weaken h.2 us, by
      have := tyL_of_forall₂ hr (us ++ [τ])
      simpa using this⟩

lemma getD_append_len (τs us : List Ty) (τ : Ty) (j : ℕ) :
    (τs ++ τ :: us).getD (τs.length + j) (P 0 0) = (τ :: us).getD j (P 0 0) := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  congr 1; omega

lemma hasCost_bindSub {n : ℕ} {a b : Xp} {τb : Ty} {g : Gn} {e₀ d₀ e d : ℕ}
    (hn : τs.length = n) (ha : HasTy τs a (P e₀ d₀)) (hab : a.Bnd n) (hb : HasTy τs b τb)
    (hbb : b.Bnd n) (hg : HasCost (τs ++ [P e₀ d₀]) g e d) :
    HasCost τs (bindSub n a b g) (max e₀ e) (max d₀ d) := by
  have ha' := ha.weaken' hn hab [P 0 0]
  have hb' := hb.weaken' hn hbb ([P 0 0] ++ [P e₀ d₀, P e₀ d₀])
  have hv : HasTy ((τs ++ [P 0 0]) ++ [P e₀ d₀, P e₀ d₀]) (var (n + 2)) (P e₀ d₀) := by
    refine hasTy_var' ?_
    have := getD_append_len τs [P e₀ d₀, P e₀ d₀] (P 0 0) 2
    simpa [← hn] using this
  have hbody : HasCost ((τs ++ [P 0 0]) ++ [P e₀ d₀, P e₀ d₀])
      (when (Xp.lt b (Xp.add (Xp.var (n + 2)) (Xp.const 1))) (emit (Xp.const 0))) 0 0 := by
    refine hasCost_when (hasTy_lt (by simpa using hb') (hasTy_addBig hv (hasTy_const 1)))
      (hasCost_emit (hasTy_const 0))
  have hloop := hasCost_loop ha' hbody
  have hlen : HasLen (τs ++ [P 0 0]) (loop a (when (Xp.lt b (Xp.add (Xp.var (n + 2))
      (Xp.const 1))) (emit (Xp.const 0)))) (P e₀ d₀) := by
    have := hasLen_loop ha' (hasLen_when (Xp.lt b (Xp.add (Xp.var (n + 2)) (Xp.const 1)))
      (hasLen_emit (τs := (τs ++ [P 0 0]) ++
      [P e₀ d₀, P e₀ d₀]) (Xp.const 0)))
    simpa using this
  refine hasCost_count (hloop.mono (by omega) (by omega)) hlen
    (hg.mono (le_max_right _ _) (le_max_right _ _))

end Gn

end Lax119563Proofs.Reduction

end Reduction_CostGn

/-! ### Formerly `Lax119563Proofs.Reduction.CostMachine` -/

section Reduction_CostMachine

/-!
# Lengths of encodings

`length_encodeNat_le`, `length_encodeNats_le`: bounds on the length of the binary encoding of
numbers and lists of numbers.
-/

open Lax119563.BinaryEncodings Lax119563.DeterministicTime

namespace Lax119563Proofs.Reduction

open Ty

lemma length_encodeNat_le {v w : ℕ} (h : v < 2 ^ w) : (encodeNat v).length ≤ 2 * w + 1 := by
  simp only [encodeNat, List.length_append, List.length_flatMap, List.length_cons,
    List.length_nil]
  have : (Nat.bits v).length ≤ w := by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr h
  have e : ((Nat.bits v).map fun _ => 2).sum = 2 * (Nat.bits v).length := by
    simp [Nat.mul_comm]
  simp only [zero_add, Nat.reduceAdd] at *
  rw [e]; omega

lemma length_encodeNats_le {l : List ℕ} {w : ℕ} (h : ∀ v ∈ l, v < 2 ^ w) :
    (encodeNats l).length ≤ l.length * (2 * w + 1) := by
  induction l with
  | nil => simp [encodeNats]
  | cons v l ih =>
    simp only [encodeNats, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have h1 := length_encodeNat_le (h v (by simp))
    have h2 := ih fun u hu => h u (by simp [hu])
    nlinarith

namespace Gn

end Gn

end Lax119563Proofs.Reduction

end Reduction_CostMachine

/-! ### Formerly `Lax119563Proofs.Reduction.SymLoc` -/

section Reduction_SymLoc

/-!
# Symbolic locations and moves

Locations and moves of the verifier whose runtime fields (depths `d`, `u`) are expressions
`Xp` over the generator stack, while the constant-size fields are Lean values.
* `SLoc M`, `SLoc.eval H ρ : Loc M H` (runtime fields clamped to `≤ H` by `finH`),
  `SLoc.codeX R HX`: an expression for the location number (runtime fields clamped by
  `minX`); `SLoc.eval_codeX`: it evaluates to `Loc.code` when `R, HX` evaluate to
  `radix M H, H`.
* `SMv M s`: symbolic moves (`step`, `fork`, and the two kinds of tests), `SMv.eval` to a
  `Move`, and `SMv.recX R HX`: the eight numbers describing the command of the move
  (`CmdDesc`): kind (`0` assign, `1` fork), mask, the target location number(s), and the
  guard (`GDesc`: `0, k, m, q` for `fieldGuard ℓ k m q`, `1, ν, encCV c` for
  `hitGuard ν c`, `2, i` for `missGuard i`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime

variable {M : Machine}

/-- A natural number clamped into `Fin (H + 1)`. -/
def finH (H v : ℕ) : Fin (H + 1) := ⟨min v H, by omega⟩

lemma finH_val {H v : ℕ} (h : v ≤ H) : (finH H v).val = v := by simp [finH, h]

lemma finH_eq {H : ℕ} {v : ℕ} {d : Fin (H + 1)} (h : v = d.val) : finH H v = d :=
  Fin.ext (by simp only [finH]; have := d.isLt; omega)

open Xp in
/-- `min a h`. -/
def minX (a h : Xp) : Xp :=
  add (mul a (lt a (add h (const 1)))) (mul h (Xp.not (lt a (add h (const 1)))))

@[simp] lemma eval_minX {ρ : List ℕ} (a h : Xp) : (minX a h).eval ρ = min (a.eval ρ) (h.eval ρ) := by
  simp only [minX, Xp.eval_add, Xp.eval_mul]
  show a.eval ρ * (if a.eval ρ < h.eval ρ + 1 then 1 else 0) +
    h.eval ρ * (if (if a.eval ρ < h.eval ρ + 1 then 1 else 0) < 1 then 1 else 0) = _
  by_cases hc : a.eval ρ < h.eval ρ + 1 <;> simp [hc] <;> omega

lemma bnd_minX {n : ℕ} {a h : Xp} (ha : a.Bnd n) (hh : h.Bnd n) : (minX a h).Bnd n :=
  ⟨Xp.bnd_mul ha ⟨ha, hh, trivial⟩, Xp.bnd_mul hh ⟨⟨ha, hh, trivial⟩, trivial⟩⟩

/-! ## Symbolic locations -/

/-- Locations with runtime depth fields given by expressions. -/
inductive SLoc (M : Machine)
  | accept
  | reject
  | query
  | cell (d : Xp) (θ : Fin 3) (ν : Tape M) (c : CellVal M)
  | state (d : Xp) (θ : Fin 3) (p : ExtState M)
  | headIn (d : Xp) (θ : Fin 2) (ν : Tape M) (u : Xp)
  | headSet (d : Xp) (θ : Fin 2) (ν : Tape M) (β : Fin 8)
  | restore (d : Xp) (θ : Fin 2) (ν : Tape M) (c : CellVal M) (β : Fin 8)
  | gather (d : Xp) (θ : Fin 2) (ν : Tape M) (c : CellVal M) (β : Fin 8)
  | baseCell (ν : Tape M) (ρ : Row M) (old : CellVal M) (k : Fin (M.tapes + 2))
  | baseState (ρ : Row M) (k : Fin (M.tapes + 2))
  | setJ (ν : Tape M) (h : Fin 4) (c : CellVal M)

namespace SLoc

/-- The location denoted on the stack `ρ`. -/
def eval (H : ℕ) (ρ : List ℕ) : SLoc M → Loc M H
  | accept => .accept
  | reject => .reject
  | query => .query
  | cell d θ ν c => .cell (finH H (d.eval ρ)) θ ν c
  | state d θ p => .state (finH H (d.eval ρ)) θ p
  | headIn d θ ν u => .headIn (finH H (d.eval ρ)) θ ν (finH H (u.eval ρ))
  | headSet d θ ν β => .headSet (finH H (d.eval ρ)) θ ν β
  | restore d θ ν c β => .restore (finH H (d.eval ρ)) θ ν c β
  | gather d θ ν c β => .gather (finH H (d.eval ρ)) θ ν c β
  | baseCell ν ρ' old k => .baseCell ν ρ' old k
  | baseState ρ' k => .baseState ρ' k
  | setJ ν h c => .setJ ν h c

/-- The expressions read only stack levels below `n`. -/
def Bnd (n : ℕ) : SLoc M → Prop
  | cell d .. => d.Bnd n
  | state d .. => d.Bnd n
  | headIn d _ _ u => d.Bnd n ∧ u.Bnd n
  | headSet d .. => d.Bnd n
  | restore d .. => d.Bnd n
  | gather d .. => d.Bnd n
  | _ => True

/-- The tag of the location number. -/
def tag : SLoc M → ℕ
  | accept => 0
  | reject => 1
  | query => 2
  | cell .. => 3
  | state .. => 4
  | headIn .. => 5
  | headSet .. => 6
  | restore .. => 7
  | gather .. => 8
  | baseCell .. => 9
  | baseState .. => 10
  | setJ .. => 11

open Xp in
/-- The five fields of the location number (runtime fields clamped to `≤ H`). -/
def flds (HX : Xp) : SLoc M → Xp × Xp × Xp × Xp × Xp
  | accept => (const 0, const 0, const 0, const 0, const 0)
  | reject => (const 0, const 0, const 0, const 0, const 0)
  | query => (const 0, const 0, const 0, const 0, const 0)
  | cell d θ ν c => (minX d HX, const θ, const ν, const (encCV c), const 0)
  | state d θ p => (minX d HX, const θ, const (encExt p), const 0, const 0)
  | headIn d θ ν u => (minX d HX, const θ, const ν, minX u HX, const 0)
  | headSet d θ ν β => (minX d HX, const θ, const ν, const β, const 0)
  | restore d θ ν c β => (minX d HX, const θ, const ν, const (encCV c), const β)
  | gather d θ ν c β => (minX d HX, const θ, const ν, const (encCV c), const β)
  | baseCell ν ρ old k => (const ν, const (encRow ρ), const (encCV old), const k, const 0)
  | baseState ρ k => (const (encRow ρ), const k, const 0, const 0, const 0)
  | setJ ν h c => (const ν, const h, const (encCV c), const 0, const 0)

open Xp in
/-- The location number in mixed radix `16, R, C, C, R, C` (`C = cM M`). -/
def codeX (R HX : Xp) (L : SLoc M) : Xp :=
  add (const L.tag) (mulC 16 (add (L.flds HX).1 (mul (add (L.flds HX).2.1 (mulC (cM M) (add
    (L.flds HX).2.2.1 (mulC (cM M) (add (L.flds HX).2.2.2.1 (mul (L.flds HX).2.2.2.2 R)))))) R)))

lemma bnd_codeX {n : ℕ} {R HX : Xp} (hR : R.Bnd n) (hH : HX.Bnd n) (L : SLoc M)
    (hL : L.Bnd n) : (codeX R HX L).Bnd n := by
  have h0 : ∀ c, (Xp.const c).Bnd n := fun _ => trivial
  have hm : ∀ {a : Xp}, a.Bnd n → (minX a HX).Bnd n := fun ha => bnd_minX ha hH
  have hf : (L.flds HX).1.Bnd n ∧ (L.flds HX).2.1.Bnd n ∧ (L.flds HX).2.2.1.Bnd n ∧
      (L.flds HX).2.2.2.1.Bnd n ∧ (L.flds HX).2.2.2.2.Bnd n := by
    cases L <;> simp only [flds, Bnd] at hL ⊢ <;>
      first
      | exact ⟨h0 _, h0 _, h0 _, h0 _, h0 _⟩
      | exact ⟨hm hL, h0 _, h0 _, h0 _, h0 _⟩
      | exact ⟨hm hL.1, h0 _, h0 _, hm hL.2, h0 _⟩
  obtain ⟨f1, f2, f3, f4, f5⟩ := hf
  refine ⟨trivial, Xp.bnd_mulC ?_ 16⟩
  refine ⟨f1, Xp.bnd_mul ?_ hR⟩
  refine ⟨f2, Xp.bnd_mulC ?_ _⟩
  refine ⟨f3, Xp.bnd_mulC ?_ _⟩
  exact ⟨f4, Xp.bnd_mul f5 hR⟩

lemma eval_codeX {H : ℕ} {R HX : Xp} {ρ : List ℕ} (hR : R.eval ρ = radix M H)
    (hH : HX.eval ρ = H) (L : SLoc M) :
    (codeX R HX L).eval ρ = (Loc.code (L.eval H ρ)).val := by
  cases L <;>
    simp only [codeX, flds, tag, eval, Loc.code, Loc.tuple, pack, Xp.eval_add, eval_minX,
      Xp.eval_mulC, Xp.eval_mul, Xp.eval_const, hR, hH, finH] <;> ring

end SLoc

/-! ## Symbolic moves -/

/-- Moves with runtime field positions given by expressions. -/
inductive SMv (M : Machine) (s : ℕ)
  | step (k : Xp) (m q v : ℕ) (dst : SLoc M)
  | fork (k : Xp) (m q : ℕ) (l r : SLoc M)
  | hit (ν : Tape M) (c : CellVal M) (dst : SLoc M)
  | miss (i : Fin s) (dst : SLoc M)

namespace SMv

variable {s : ℕ}

/-- The move denoted on the stack `ρ`. -/
def eval (M : Machine) (x : List Bool) (s ℓ H : ℕ) (ρ : List ℕ) :
    SMv M s → Move (Loc M H) s
  | step k m q v dst => .step (k.eval ρ) m q v (dst.eval H ρ)
  | fork k m q l r => .fork (k.eval ρ) m q (l.eval H ρ) (r.eval H ρ)
  | hit ν c dst => .test (hitGuard M x s ℓ H ν c) (dst.eval H ρ)
  | miss i dst => .test (missGuard s ℓ H i) (dst.eval H ρ)

/-- The expressions read only stack levels below `n`. -/
def Bnd (n : ℕ) : SMv M s → Prop
  | step k _ _ _ dst => k.Bnd n ∧ dst.Bnd n
  | fork k _ _ l r => k.Bnd n ∧ l.Bnd n ∧ r.Bnd n
  | hit _ _ dst => dst.Bnd n
  | miss _ dst => dst.Bnd n

open Xp in
/-- The eight numbers of the command of a move. -/
def recX (R HX : Xp) : SMv M s → List Xp
  | step k m q v dst => [const 0, shl (const (q ^^^ v)) k, dst.codeX R HX, const 0,
      const 0, k, const m, const q]
  | fork k m q l r => [const 1, const 0, l.codeX R HX, r.codeX R HX, const 0, k, const m, const q]
  | hit ν c dst => [const 0, const 0, dst.codeX R HX, const 0, const 1, const ν, const (encCV c),
      const 0]
  | miss i dst => [const 0, const 0, dst.codeX R HX, const 0, const 2, const i, const 0, const 0]

lemma bnd_rec {n : ℕ} {R HX : Xp} (hR : R.Bnd n) (hH : HX.Bnd n) (m : SMv M s)
    (hm : m.Bnd n) : ∀ e ∈ m.recX R HX, e.Bnd n := by
  cases m with
  | step k m q v dst =>
    simp only [recX, List.mem_cons, List.not_mem_nil, or_false]
    rintro e (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals first | trivial | exact ⟨trivial, hm.1⟩ | exact SLoc.bnd_codeX hR hH _ hm.2 | exact hm.1
  | fork k m q l r =>
    simp only [recX, List.mem_cons, List.not_mem_nil, or_false]
    rintro e (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals first | trivial | exact SLoc.bnd_codeX hR hH _ hm.2.1 |
      exact SLoc.bnd_codeX hR hH _ hm.2.2 | exact hm.1
  | hit ν c dst =>
    simp only [recX, List.mem_cons, List.not_mem_nil, or_false]
    rintro e (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals first | trivial | exact SLoc.bnd_codeX hR hH _ hm
  | miss i dst =>
    simp only [recX, List.mem_cons, List.not_mem_nil, or_false]
    rintro e (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals first | trivial | exact SLoc.bnd_codeX hR hH _ hm

end SMv

/-! ## Numeric descriptions of commands -/

section Desc

variable (M : Machine) (x : List Bool) (s ℓ H : ℕ)

/-- The four numbers `gd` describe the guard `g`. -/
def GDesc (g : Fin s → ℕ → Bool) (gd : List ℕ) : Prop :=
  (gd.getD 0 0 = 0 ∧ g = fieldGuard ℓ (gd.getD 1 0) (gd.getD 2 0) (gd.getD 3 0)) ∨
  (gd.getD 0 0 = 1 ∧ ∃ (ν : Tape M) (c : CellVal M), ν.val = gd.getD 1 0 ∧
    encCV c = gd.getD 2 0 ∧ g = hitGuard M x s ℓ H ν c) ∨
  (gd.getD 0 0 = 2 ∧ ∃ i : Fin s, i.val = gd.getD 1 0 ∧ g = missGuard s ℓ H i)

/-- The eight numbers `r` describe the command (without its source). -/
def CmdDesc : ACmd (Loc M H) s → List ℕ → Prop
  | .assign _ g m q, r => r.length = 8 ∧ r.getD 0 0 = 0 ∧ r.getD 1 0 = m ∧
      r.getD 2 0 = (Loc.code q).val ∧ GDesc M x s ℓ H g (r.drop 4)
  | .fork _ g q q', r => r.length = 8 ∧ r.getD 0 0 = 1 ∧ r.getD 2 0 = (Loc.code q).val ∧
      r.getD 3 0 = (Loc.code q').val ∧ GDesc M x s ℓ H g (r.drop 4)

end Desc

lemma SMv.desc {s ℓ H : ℕ} {x : List Bool} {R HX : Xp} {ρ : List ℕ} (hR : R.eval ρ = radix M H)
    (hH : HX.eval ρ = H) (src : Loc M H) (m : SMv M s) :
    CmdDesc M x s ℓ H (Move.toACmd ℓ src (m.eval M x s ℓ H ρ)) ((m.recX R HX).map (·.eval ρ)) := by
  cases m with
  | step k m q v dst =>
    refine ⟨rfl, rfl, ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
    · simp [recX, fieldMask, Nat.shiftLeft_eq]
    · simp [recX, SLoc.eval_codeX hR hH]
  | fork k m q l r =>
    exact ⟨rfl, rfl, by simp [recX, SLoc.eval_codeX hR hH],
      by simp [recX, SLoc.eval_codeX hR hH], Or.inl ⟨rfl, rfl⟩⟩
  | hit ν c dst =>
    exact ⟨rfl, rfl, rfl, by simp [recX, SLoc.eval_codeX hR hH],
      Or.inr (Or.inl ⟨rfl, ν, c, rfl, rfl, rfl⟩)⟩
  | miss i dst =>
    exact ⟨rfl, rfl, rfl, by simp [recX, SLoc.eval_codeX hR hH],
      Or.inr (Or.inr ⟨rfl, i, rfl, rfl⟩)⟩

end Lax119563Proofs.Reduction

end Reduction_SymLoc

/-! ### Formerly `Lax119563Proofs.Reduction.SymMoves` -/

section Reduction_SymMoves

/-!
# The moves of the verifier as symbolic branch lists

For each location kind and constant fields, `brs V …` is a list of branches
`(condition, moves)`: the moves of the location are those of the first branch whose condition
evaluates to a nonzero value (`selBr`). The runtime values (depth `d`, head position `u`,
`d - 1`, `u - 1`, `H - d - 1`, `H + 2 - d`, `H`) are expressions `V : RVals`.

`moves_eq`: if `V` evaluates correctly (`RVals.Ok`), the selected branch, evaluated, is the
list of moves of the location (`Loc.ofS`); `ok_sel`: its targets have runtime fields `≤ H`.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp

variable {M : Machine} {s : ℕ}

/-- Expressions for the runtime values of a location. -/
structure RVals where
  d : Xp
  u : Xp
  dm1 : Xp
  um1 : Xp
  hd1 : Xp
  hd2 : Xp
  H : Xp

/-- The expressions evaluate to `d, u, d - 1, u - 1, H - d - 1, H + 2 - d, H`. -/
structure RVals.Ok (V : RVals) (H₀ : ℕ) (ρ : List ℕ) (d₀ u₀ : ℕ) : Prop where
  d : V.d.eval ρ = d₀
  u : V.u.eval ρ = u₀
  dm1 : V.dm1.eval ρ = d₀ - 1
  um1 : V.um1.eval ρ = u₀ - 1
  hd1 : V.hd1.eval ρ = H₀ - d₀ - 1
  hd2 : V.hd2.eval ρ = H₀ + 2 - d₀
  H : V.H.eval ρ = H₀

/-- All expressions read only levels below `n`. -/
structure RVals.Bnd (V : RVals) (n : ℕ) : Prop where
  d : V.d.Bnd n
  u : V.u.Bnd n
  dm1 : V.dm1.Bnd n
  um1 : V.um1.Bnd n
  hd1 : V.hd1.Bnd n
  hd2 : V.hd2.Bnd n
  H : V.H.Bnd n

/-- The moves of the first branch whose condition holds. -/
def selBr {α : Type} (ρ : List ℕ) : List (Xp × List α) → List α
  | [] => []
  | (c, ms) :: rest => if c.eval ρ ≠ 0 then ms else selBr ρ rest

/-- The location kinds with their constant fields. -/
inductive SKind (M : Machine)
  | accept
  | reject
  | query
  | cell (θ : Fin 3) (ν : Tape M) (c : CellVal M)
  | state (θ : Fin 3) (p : ExtState M)
  | headIn (θ : Fin 2) (ν : Tape M)
  | headSet (θ : Fin 2) (ν : Tape M) (β : Fin 8)
  | restore (θ : Fin 2) (ν : Tape M) (c : CellVal M) (β : Fin 8)
  | gather (θ : Fin 2) (ν : Tape M) (c : CellVal M) (β : Fin 8)
  | baseCell (ν : Tape M) (ρ : Row M) (old : CellVal M) (k : Fin (M.tapes + 2))
  | baseState (ρ : Row M) (k : Fin (M.tapes + 2))
  | setJ (ν : Tape M) (h : Fin 4) (c : CellVal M)

/-- The location of a kind with runtime values `d, u`. -/
def SKind.loc (H d u : ℕ) : SKind M → Loc M H
  | accept => .accept
  | reject => .reject
  | query => .query
  | cell θ ν c => .cell (finH H d) θ ν c
  | state θ p => .state (finH H d) θ p
  | headIn θ ν => .headIn (finH H d) θ ν (finH H u)
  | headSet θ ν β => .headSet (finH H d) θ ν β
  | restore θ ν c β => .restore (finH H d) θ ν c β
  | gather θ ν c β => .gather (finH H d) θ ν c β
  | baseCell ν ρ old k => .baseCell ν ρ old k
  | baseState ρ k => .baseState ρ k
  | setJ ν h c => .setJ ν h c

/-- `goto` and unconditional forks. -/
def SMv.goto (dst : SLoc M) : SMv M s := .step (const 0) 0 0 0 dst
/-- An unconditional fork. -/
def SMv.fork' (l r : SLoc M) : SMv M s := .fork (const 0) 0 0 l r

/-- The branches of the moves of a kind. -/
def SKind.brs (V : RVals) : SKind M → List (Xp × List (SMv M s))
  | accept => []
  | reject => []
  | query => [(const 1, ((allExt M).filter fun p => decide (p.2 = some true)).map fun p =>
      SMv.goto (.state (const 0) 2 p))]
  | cell θ ν c =>
    if θ.val = 0 then
      [(eq V.d (const 0), SMv.hit ν c .accept ::
          (if c = (0, false) then
            ((List.finRange s).filter fun i => decide (i.val ≠ 0)).map fun i => SMv.miss i .accept
          else [])),
        (const 1, (List.finRange 2).flatMap fun (θ' : Fin 2) => (List.finRange 8).map fun β =>
          SMv.fork V.hd2 1 θ'.val (.headSet V.dm1 θ' ν β) (.gather V.dm1 θ' ν c β))]
    else
      [(lt V.d V.H, (List.finRange 8).map fun β =>
          SMv.fork' (.headSet V.d (ppred θ) ν β) (.restore V.d (ppred θ) ν c β)),
        (const 1, if θ.val = 2 then
          (allRows M).flatMap fun ρ => (allCV M).flatMap fun old =>
            ((List.finRange 4).filter fun jj =>
              decide (nextCell ρ.1 ρ.2.2 ν ((ρ.2.1 ν).val + 1 : ℤ) (jj.val : ℤ) old = c)).map
            fun jj => SMv.step (const 0) 2 jj.val jj.val (.baseCell ν ρ old 0)
          else [])]
  | state θ p =>
    if θ.val = 0 then
      [(eq V.d (const 0), if p = (0, none) then [SMv.goto .accept] else []),
        (const 1, (List.finRange 2).map fun (θ' : Fin 2) =>
          SMv.step V.hd2 1 θ'.val θ'.val (.state V.dm1 θ'.castSucc p))]
    else
      [(lt V.d V.H, (List.finRange 2).map fun (e : Fin 2) =>
          SMv.step (add V.hd1 (const 2)) 1 e.val (ppred θ).val
            (.state (add V.d (const 1)) 2 p)),
        (const 1, if θ.val = 2 then
          ((allRows M).filter fun ρ => decide (nextExt ρ.1 ρ.2.2 = p)).map fun ρ =>
            SMv.goto (.baseState ρ 0)
          else [])]
  | headIn θ ν =>
    [(and (lt (add V.u V.d) V.H) (eq V.u (const 0)),
        (List.finRange (M.symbols + 3)).map fun γ => SMv.goto (.cell V.d θ.castSucc ν (γ, true))),
      (lt (add V.u V.d) V.H, (List.finRange 2).flatMap fun (e : Fin 2) =>
        (List.finRange 2).map fun (e' : Fin 2) =>
          SMv.step V.um1 1 e.val e'.val (.headIn V.d θ ν V.um1))]
  | headSet θ ν β =>
    [(lt V.d V.H, (List.finRange 8).map fun (q : Fin 8) =>
        SMv.step V.hd1 3 q.val β.val (.headIn V.d θ ν V.hd1))]
  | restore θ ν c β =>
    [(lt V.d V.H, (List.finRange 8).map fun (q : Fin 8) =>
        if sel β ≤ q.val ∧ q.val < sel β + 4 then
          SMv.step V.hd1 3 q.val (4 * θ.val + (q.val - sel β)) (.cell (add V.d (const 1)) 2 ν c)
        else SMv.step V.hd1 3 q.val q.val (.cell V.d θ.castSucc ν c))]
  | gather θ ν c β =>
    [(lt V.d V.H, (List.finRange 4).map fun (c' : Fin 4) =>
        SMv.step V.hd1 3 (4 * θ.val + c'.val) (sel β + c'.val) (.cell V.d θ.castSucc ν c))]
  | baseCell ν ρ old k =>
    [(const 1, if h : k.val < M.tapes + 1 then
        [SMv.fork' (.setJ ⟨k.val, h⟩ ⟨(ρ.2.1 ⟨k.val, h⟩).val + 1, by omega⟩
          (ρ.2.2 ⟨k.val, h⟩, true)) (.baseCell ν ρ old ⟨k.val + 1, by omega⟩)]
      else [SMv.fork' (.state V.H 0 ρ.1) (.cell V.H 0 ν old)])]
  | baseState ρ k =>
    [(const 1, if h : k.val < M.tapes + 1 then
        [SMv.fork' (.setJ ⟨k.val, h⟩ ⟨(ρ.2.1 ⟨k.val, h⟩).val + 1, by omega⟩
          (ρ.2.2 ⟨k.val, h⟩, true)) (.baseState ρ ⟨k.val + 1, by omega⟩)]
      else [SMv.goto (.state V.H 0 ρ.1)])]
  | setJ ν h c =>
    [(const 1, (List.finRange 4).map fun (q : Fin 4) =>
        SMv.step (const 0) 2 q.val h.val (.cell V.H 0 ν c))]

/-- The kind has runtime values in range: `d ≤ H`, and `u ≤ H` for `headIn`. -/
def SKind.Valid (H d u : ℕ) : SKind M → Prop
  | cell .. | state .. | headSet .. | restore .. | gather .. => d ≤ H
  | headIn .. => d ≤ H ∧ u ≤ H
  | _ => True

/-- The symbolic location of a kind, with runtime values `dX, uX`. -/
def SKind.sloc (dX uX : Xp) : SKind M → SLoc M
  | accept => .accept
  | reject => .reject
  | query => .query
  | cell θ ν c => .cell dX θ ν c
  | state θ p => .state dX θ p
  | headIn θ ν => .headIn dX θ ν uX
  | headSet θ ν β => .headSet dX θ ν β
  | restore θ ν c β => .restore dX θ ν c β
  | gather θ ν c β => .gather dX θ ν c β
  | baseCell ν ρ old k => .baseCell ν ρ old k
  | baseState ρ k => .baseState ρ k
  | setJ ν h c => .setJ ν h c

lemma SKind.eval_sloc {H : ℕ} {ρ : List ℕ} (dX uX : Xp) (K : SKind M) :
    (K.sloc dX uX).eval H ρ = K.loc H (dX.eval ρ) (uX.eval ρ) := by
  cases K <;> rfl

/-- The kinds with tag `t`. -/
def kindsOfTag (M : Machine) : ℕ → List (SKind M)
  | 0 => [.accept]
  | 1 => [.reject]
  | 2 => [.query]
  | 3 => (List.finRange 3 ×ˢ (List.finRange (M.tapes + 1) ×ˢ allCV M)).map
      fun a => .cell a.1 a.2.1 a.2.2
  | 4 => (List.finRange 3 ×ˢ allExt M).map fun a => .state a.1 a.2
  | 5 => (List.finRange 2 ×ˢ List.finRange (M.tapes + 1)).map fun a => .headIn a.1 a.2
  | 6 => (List.finRange 2 ×ˢ (List.finRange (M.tapes + 1) ×ˢ List.finRange 8)).map
      fun a => .headSet a.1 a.2.1 a.2.2
  | 7 => (List.finRange 2 ×ˢ (List.finRange (M.tapes + 1) ×ˢ (allCV M ×ˢ List.finRange 8))).map
      fun a => .restore a.1 a.2.1 a.2.2.1 a.2.2.2
  | 8 => (List.finRange 2 ×ˢ (List.finRange (M.tapes + 1) ×ˢ (allCV M ×ˢ List.finRange 8))).map
      fun a => .gather a.1 a.2.1 a.2.2.1 a.2.2.2
  | 9 => (List.finRange (M.tapes + 1) ×ˢ (allRows M ×ˢ (allCV M ×ˢ
      List.finRange (M.tapes + 2)))).map fun a => .baseCell a.1 a.2.1 a.2.2.1 a.2.2.2
  | 10 => (allRows M ×ˢ List.finRange (M.tapes + 2)).map fun a => .baseState a.1 a.2
  | 11 => (List.finRange (M.tapes + 1) ×ˢ (List.finRange 4 ×ˢ allCV M)).map
      fun a => .setJ a.1 a.2.1 a.2.2
  | _ => []

/-- The kind of a location. -/
def _root_.Lax119563Proofs.Circuits.Loc.kind {H : ℕ} : Loc M H → SKind M
  | .accept => .accept
  | .reject => .reject
  | .query => .query
  | .cell _ θ ν c => .cell θ ν c
  | .state _ θ p => .state θ p
  | .headIn _ θ ν _ => .headIn θ ν
  | .headSet _ θ ν β => .headSet θ ν β
  | .restore _ θ ν c β => .restore θ ν c β
  | .gather _ θ ν c β => .gather θ ν c β
  | .baseCell ν ρ old k => .baseCell ν ρ old k
  | .baseState ρ k => .baseState ρ k
  | .setJ ν h c => .setJ ν h c

lemma _root_.Lax119563Proofs.Circuits.Loc.kind_spec {H : ℕ} (L : Loc M H) :
    L.kind ∈ kindsOfTag M L.tuple.1 ∧
      L.kind.Valid H L.tuple.2.1 L.tuple.2.2.2.2.1 ∧
      L.kind.loc H L.tuple.2.1 L.tuple.2.2.2.2.1 = L := by
  cases L with
  | accept => exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple], trivial, rfl⟩
  | reject => exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple], trivial, rfl⟩
  | query => exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple], trivial, rfl⟩
  | cell d θ ν c =>
    exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple, List.mem_product],
      by have := d.isLt; simp only [Loc.kind, Loc.tuple, SKind.Valid]; omega,
      by simp only [Loc.kind, Loc.tuple, SKind.loc, finH_eq rfl]⟩
  | state d θ p =>
    exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple, List.mem_product],
      by have := d.isLt; simp only [Loc.kind, Loc.tuple, SKind.Valid]; omega,
      by simp only [Loc.kind, Loc.tuple, SKind.loc, finH_eq rfl]⟩
  | headIn d θ ν u =>
    exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple, List.mem_product],
      by have := d.isLt; have := u.isLt; simp only [Loc.kind, Loc.tuple, SKind.Valid]; omega,
      by simp only [Loc.kind, Loc.tuple, SKind.loc, finH_eq rfl]⟩
  | headSet d θ ν β =>
    exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple, List.mem_product],
      by have := d.isLt; simp only [Loc.kind, Loc.tuple, SKind.Valid]; omega,
      by simp only [Loc.kind, Loc.tuple, SKind.loc, finH_eq rfl]⟩
  | restore d θ ν c β =>
    exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple, List.mem_product],
      by have := d.isLt; simp only [Loc.kind, Loc.tuple, SKind.Valid]; omega,
      by simp only [Loc.kind, Loc.tuple, SKind.loc, finH_eq rfl]⟩
  | gather d θ ν c β =>
    exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple, List.mem_product],
      by have := d.isLt; simp only [Loc.kind, Loc.tuple, SKind.Valid]; omega,
      by simp only [Loc.kind, Loc.tuple, SKind.loc, finH_eq rfl]⟩
  | baseCell ν ρ old k =>
    exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple, List.mem_product], trivial, rfl⟩
  | baseState ρ k =>
    exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple, List.mem_product], trivial, rfl⟩
  | setJ ν h c =>
    exact ⟨by simp [kindsOfTag, Loc.kind, Loc.tuple, List.mem_product], trivial, rfl⟩

lemma tag_of_mem_kindsOfTag {t : ℕ} {K : SKind M} (h : K ∈ kindsOfTag M t) {H d u : ℕ} :
    (K.loc H d u).tuple.1 = t := by
  rcases t with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | t <;>
    simp only [kindsOfTag, List.mem_map, List.mem_singleton, List.not_mem_nil] at h <;>
    first
    | (subst h; rfl)
    | (obtain ⟨a, -, rfl⟩ := h; rfl)
    | exact h.elim

section Correct

variable {x : List Bool} {ℓ H : ℕ} {ρ : List ℕ} {V : RVals} {d u : ℕ}

lemma finH_dpred (hd : d ≤ H) (_h0 : d ≠ 0) :
    finH H (d - 1) = dpred (finH H d) := Fin.ext (by simp [finH, dpred]; omega)

lemma finH_zero : finH H 0 = 0 := Fin.ext (by simp [finH])

lemma finH_dsucc (hd : d < H) :
    finH H (d + 1) = dsucc (finH H d) (by simp [finH]; omega) :=
  Fin.ext (by simp [finH, dsucc]; omega)

lemma finH_self : finH H H = ⟨H, by omega⟩ := Fin.ext (by simp [finH])

lemma selBr_cons {α : Type} (c : Xp) (ms : List α) (rest : List (Xp × List α)) :
    selBr ρ ((c, ms) :: rest) = if c.eval ρ ≠ 0 then ms else selBr ρ rest := rfl

/-- **The symbolic moves are the moves.** -/
theorem moves_eq (hV : V.Ok H ρ d u) (K : SKind M) (hK : K.Valid H d u) :
    (selBr ρ (K.brs (s := s) V)).map (SMv.eval M x s ℓ H ρ) = moves M x s ℓ H (K.loc H d u) := by
  have e1 := hV.d; have e2 := hV.u; have e3 := hV.dm1; have e4 := hV.um1; have e5 := hV.hd1
  have e6 := hV.hd2; have e7 := hV.H
  cases K with
  | accept => rfl
  | reject => rfl
  | query =>
    simp only [SKind.brs, SKind.loc, moves, selBr_cons, Xp.eval_const, ne_eq, one_ne_zero,
      not_false_eq_true, if_true, List.map_map]
    refine List.map_congr_left fun p _ => ?_
    simp [SMv.eval, SMv.goto, Move.goto, SLoc.eval, finH_zero]
  | cell θ ν c =>
    have hd : (finH H d).val = d := finH_val hK
    simp only [SKind.brs, SKind.loc, moves, hd]
    by_cases hθ : θ.val = 0
    · rw [if_pos hθ, if_pos hθ]
      by_cases h0 : d = 0
      · rw [if_pos h0, selBr_cons, if_pos (by simp [e1, h0])]
        by_cases hc : c = (0, false)
        · rw [if_pos hc, if_pos hc, List.map_cons, List.map_map]
          rfl
        · rw [if_neg hc, if_neg hc]
          simp [SMv.eval, SLoc.eval]
      · rw [if_neg h0, selBr_cons, if_neg (by simp [e1, h0]), selBr_cons, if_pos (by simp),
          List.map_flatMap]
        refine List.flatMap_congr fun θ' _ => ?_
        rw [List.map_map]
        refine List.map_congr_left fun β _ => ?_
        simp only [Function.comp, SMv.eval, SLoc.eval, e3, e6, finH_dpred hK h0, bpos]
        congr 1
        omega
    · rw [if_neg hθ, if_neg hθ]
      by_cases hlt : d < H
      · rw [dif_pos hlt, selBr_cons, if_pos (by simp [e1, e7, hlt]), List.map_map]
        refine List.map_congr_left fun β _ => ?_
        simp [SMv.eval, SMv.fork', Move.fork', SLoc.eval, e1]
      · rw [dif_neg hlt, selBr_cons, if_neg (by simp [e1, e7, hlt]), selBr_cons,
          if_pos (by simp)]
        by_cases h2 : θ.val = 2
        · rw [if_pos h2, if_pos h2, List.map_flatMap]
          refine List.flatMap_congr fun ρ' _ => ?_
          rw [List.map_flatMap]
          refine List.flatMap_congr fun old _ => ?_
          rw [List.map_map]
          refine List.map_congr_left fun jj _ => ?_
          rfl
        · rw [if_neg h2, if_neg h2]; rfl
  | state θ p =>
    have hd : (finH H d).val = d := finH_val hK
    simp only [SKind.brs, SKind.loc, moves, hd]
    by_cases hθ : θ.val = 0
    · rw [if_pos hθ, if_pos hθ]
      by_cases h0 : d = 0
      · rw [if_pos h0, selBr_cons, if_pos (by simp [e1, h0])]
        by_cases hp : p = (0, none)
        · rw [if_pos hp, if_pos hp]; rfl
        · rw [if_neg hp, if_neg hp]; rfl
      · rw [if_neg h0, selBr_cons, if_neg (by simp [e1, h0]), selBr_cons, if_pos (by simp),
          List.map_map]
        refine List.map_congr_left fun θ' _ => ?_
        simp only [Function.comp, SMv.eval, SLoc.eval, e3, e6, finH_dpred hK h0, bpos]
        congr 1
        omega
    · rw [if_neg hθ, if_neg hθ]
      by_cases hlt : d < H
      · rw [dif_pos hlt, selBr_cons, if_pos (by simp [e1, e7, hlt]), List.map_map]
        refine List.map_congr_left fun e _ => ?_
        simp only [Function.comp, SMv.eval, SLoc.eval, Xp.eval_add, Xp.eval_const, e1, e5, bpos,
          finH_dsucc hlt]
      · rw [dif_neg hlt, selBr_cons, if_neg (by simp [e1, e7, hlt]), selBr_cons,
          if_pos (by simp)]
        by_cases h2 : θ.val = 2
        · rw [if_pos h2, if_pos h2, List.map_map]
          refine List.map_congr_left fun ρ' _ => ?_
          rfl
        · rw [if_neg h2, if_neg h2]; rfl
  | headIn θ ν =>
    have hd : (finH H d).val = d := finH_val hK.1
    have hu : (finH H u).val = u := finH_val hK.2
    simp only [SKind.brs, SKind.loc, moves, hd, hu]
    have hand : ∀ a b : Xp, a.eval ρ ≤ 1 → b.eval ρ ≤ 1 →
        ((Xp.and a b).eval ρ ≠ 0 ↔ a.eval ρ = 1 ∧ b.eval ρ = 1) := fun a b ha hb => by
      rw [Xp.eval_and ha hb]; split_ifs <;> simp_all
    have l1 : (Xp.lt (Xp.add V.u V.d) V.H).eval ρ ≤ 1 := by simp only [Xp.eval_lt_eq]; split_ifs <;> omega
    have l2 : (Xp.eq V.u (Xp.const 0)).eval ρ ≤ 1 := by simp only [Xp.eval_eq]; split_ifs <;> omega
    by_cases hlt : u < H - d
    · rw [if_pos hlt]
      by_cases h0 : u = 0
      · rw [if_pos h0, selBr_cons, if_pos (by rw [hand _ _ l1 l2]; simp [e1, e2, e7, h0]; omega),
          List.map_map]
        refine List.map_congr_left fun γ _ => ?_
        simp [SMv.eval, SMv.goto, Move.goto, SLoc.eval, e1]
      · rw [if_neg h0, selBr_cons, if_neg (by rw [hand _ _ l1 l2]; simp [e2, h0]),
          selBr_cons, if_pos (by simp [e1, e2, e7]; omega), List.map_flatMap]
        refine List.flatMap_congr fun e _ => ?_
        rw [List.map_map]
        refine List.map_congr_left fun e' _ => ?_
        simp only [Function.comp, SMv.eval, SLoc.eval, e1, e4, finH_dpred hK.2 h0]
    · rw [if_neg hlt, selBr_cons, if_neg (by rw [hand _ _ l1 l2]; simp [e1, e2, e7]; omega),
        selBr_cons, if_neg (by simp [e1, e2, e7]; omega)]
      rfl
  | headSet θ ν β =>
    have hd : (finH H d).val = d := finH_val hK
    simp only [SKind.brs, SKind.loc, moves, hd]
    by_cases hlt : d < H
    · rw [if_pos hlt, selBr_cons, if_pos (by simp [e1, e7, hlt]), List.map_map]
      refine List.map_congr_left fun q _ => ?_
      simp only [Function.comp, SMv.eval, SLoc.eval, e1, e5, bpos]
      congr 2
      exact Fin.ext (by simp [finH]; omega)
    · rw [if_neg hlt, selBr_cons, if_neg (by simp [e1, e7, hlt])]; rfl
  | restore θ ν c β =>
    have hd : (finH H d).val = d := finH_val hK
    simp only [SKind.brs, SKind.loc, moves, hd]
    by_cases hlt : d < H
    · rw [dif_pos hlt, selBr_cons, if_pos (by simp [e1, e7, hlt]), List.map_map]
      refine List.map_congr_left fun q _ => ?_
      simp only [Function.comp]
      split_ifs
      · simp only [SMv.eval, SLoc.eval, Xp.eval_add, Xp.eval_const, e1, e5, bpos,
          finH_dsucc hlt]
      · simp only [SMv.eval, SLoc.eval, e1, e5, bpos]
    · rw [dif_neg hlt, selBr_cons, if_neg (by simp [e1, e7, hlt])]; rfl
  | gather θ ν c β =>
    have hd : (finH H d).val = d := finH_val hK
    simp only [SKind.brs, SKind.loc, moves, hd]
    by_cases hlt : d < H
    · rw [if_pos hlt, selBr_cons, if_pos (by simp [e1, e7, hlt]), List.map_map]
      refine List.map_congr_left fun c' _ => ?_
      simp only [Function.comp, SMv.eval, SLoc.eval, e1, e5, bpos]
    · rw [if_neg hlt, selBr_cons, if_neg (by simp [e1, e7, hlt])]; rfl
  | baseCell ν ρ' old k =>
    simp only [SKind.brs, SKind.loc, moves, selBr_cons, Xp.eval_const, ne_eq, one_ne_zero,
      not_false_eq_true, if_true]
    split_ifs
    · rfl
    · simp [SMv.eval, SMv.fork', Move.fork', SLoc.eval, e7, finH_self]
  | baseState ρ' k =>
    simp only [SKind.brs, SKind.loc, moves, selBr_cons, Xp.eval_const, ne_eq, one_ne_zero,
      not_false_eq_true, if_true]
    split_ifs
    · rfl
    · simp [SMv.eval, SMv.goto, Move.goto, SLoc.eval, e7, finH_self]
  | setJ ν h c =>
    simp only [SKind.brs, SKind.loc, moves, selBr_cons, Xp.eval_const, ne_eq, one_ne_zero,
      not_false_eq_true, if_true, List.map_map]
    refine List.map_congr_left fun q _ => ?_
    simp [SMv.eval, SLoc.eval, e7, finH_self]

end Correct

end Lax119563Proofs.Reduction

end Reduction_SymMoves

/-! ### Formerly `Lax119563Proofs.Reduction.CmdEnum` -/

section Reduction_CmdEnum

/-!
# Command records of the verifier program

Generators and stacks describing the commands of the code-ordered verifier program, location by
location: `firstL c f` runs `f a` for the first `a` with `c a ≠ 0`, `brGen RX HX body` runs
`body` for the moves of the selected branch, each with its index and command record
(`SMv.recX`). For a location `L` (location numbers in radix `R = radix M H` and `C = cM M`),
`stkL ρ H L` is the stack of the body below the move records and `recsOf L` are the records.

`desc_recsOf`: the records are `k :: rs[k]` where `rs` describes the commands of the moves of
`L` (`CmdDesc`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp

variable {M : Machine} {s : ℕ}

namespace Gn

variable {x : List Bool} {ρ : List ℕ}

/-- `f a` for the first `a ∈ l` with `c a ≠ 0`. -/
def firstL {α : Type} (c : α → Xp) (f : α → Gn) : List α → Gn
  | [] => skip
  | a :: l => ite (c a) (f a) (firstL c f l)

lemma out_firstL {α : Type} (c : α → Xp) (f : α → Gn) : ∀ l : List α,
    (firstL c f l).out x ρ =
      match l.find? (fun a => (c a).eval ρ ≠ 0) with
      | some a => (f a).out x ρ
      | none => []
  | [] => rfl
  | a :: l => by
    simp only [firstL, out, List.find?_cons]
    by_cases h : (c a).eval ρ ≠ 0
    · simp [h]
    · simp only [h, if_false, decide_false]
      exact out_firstL c f l

/-- The moves of the selected branch, each with its index and its command record. -/
def brGen (RX HX : Xp) (body : Gn) : List (Xp × List (SMv M s)) → Gn
  | [] => skip
  | (c, ms) :: rest => ite c (seqL (ms.zipIdx.map fun p =>
      bindL (Xp.const p.2 :: p.1.recX RX HX) body)) (brGen RX HX body rest)

lemma out_brGen {n : ℕ} (hρ : ρ.length = n) {RX HX : Xp} (hR : RX.Bnd n) (hH : HX.Bnd n)
    (body : Gn) :
    ∀ brs : List (Xp × List (SMv M s)), (∀ br ∈ brs, br.1.Bnd n ∧ ∀ m ∈ br.2, m.Bnd n) →
      (brGen RX HX body brs).out x ρ = (selBr ρ brs).zipIdx.flatMap fun p =>
        body.out x (ρ ++ (p.2 :: (p.1.recX RX HX).map fun e => e.eval ρ))
  | [] => fun _ => rfl
  | (c, ms) :: rest => fun h => by
    simp only [brGen, out, selBr]
    by_cases hc : c.eval ρ ≠ 0
    · simp only [hc, ne_eq, not_false_eq_true, if_true, out_seqL, List.flatMap_map]
      refine List.flatMap_congr fun p hp => ?_
      have hm : p.1 ∈ ms := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hp)
      rw [out_bindL body _ hρ ?_]
      · simp
      · intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · trivial
        · exact SMv.bnd_rec hR hH _ ((h (c, ms) (by simp)).2 _ hm) e he
    · simp only [hc, if_false]
      exact out_brGen hρ hR hH body rest fun br hbr => h br (by simp [hbr])

end Gn

/-! ## The enumerator -/

section Enum

variable (M s)

/-- The runtime values at base depth `b`. -/
def rvB (b : ℕ) (HX : Xp) : RVals :=
  ⟨var (b + 9), var (b + 3), var (b + 10), var (b + 11), var (b + 12), var (b + 13), HX⟩

/-- The stack below the source number, for the digits `t = (tag, t1, …, t5)`. -/
def stkT (ρ : List ℕ) (H R C : ℕ) (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : List ℕ :=
  ρ ++ [C, t.2.2.2.2.2, R, t.2.2.2.2.1, C, t.2.2.2.1, C, t.2.2.1, R, t.2.1,
    t.2.1 - 1, t.2.2.2.2.1 - 1, H - (t.2.1 + 1), H + 2 - t.2.1,
    pack R t.2.1 (pack C t.2.2.1 (pack C t.2.2.2.1 (pack R t.2.2.2.2.1 t.2.2.2.2.2)))]

/-- The stack of the body for the location `L`, below the move records. -/
def stkL (ρ : List ℕ) (H : ℕ) (L : Loc M H) : List ℕ :=
  stkT ρ H (radix M H) (cM M) L.tuple ++ [(Loc.code L).val]

/-- The move records of `L`: the index of the move and the numbers of its command. -/
def recsOf (b : ℕ) (HX RX : Xp) (x : List Bool) (ρ : List ℕ) (H : ℕ) (L : Loc M H) :
    List (List ℕ) :=
  (selBr (stkL M ρ H L) (L.kind.brs (s := s) (rvB b HX))).zipIdx.map fun p =>
    p.2 :: (p.1.recX RX HX).map fun e => e.eval (stkL M ρ H L)

end Enum

/-! ## Digits of location numbers -/

lemma tuple_of_code {H : ℕ} {L : Loc M H} {t t1 t2 t3 t4 t5 : ℕ} (ht : t < 16)
    (h1 : t1 < radix M H) (h2 : t2 < cM M) (h3 : t3 < cM M) (h4 : t4 < radix M H)
    (h5 : t5 < cM M)
    (h : (Loc.code L).val = pack 16 t (pack (radix M H) t1 (pack (cM M) t2
      (pack (cM M) t3 (pack (radix M H) t4 t5))))) :
    L.tuple = (t, t1, t2, t3, t4, t5) := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := L.tuple_lt
  simp only [Loc.code] at h
  obtain ⟨e0, h⟩ := pack_inj a0 ht h
  obtain ⟨e1, h⟩ := pack_inj a1 h1 h
  obtain ⟨e2, h⟩ := pack_inj a2 h2 h
  obtain ⟨e3, h⟩ := pack_inj a3 h3 h
  obtain ⟨e4, e5⟩ := pack_inj a4 h4 h
  ext <;> assumption

lemma SKind.tag_sloc {H d u : ℕ} (dX uX : Xp) (K : SKind M) :
    (K.sloc dX uX).tag = (K.loc H d u).tuple.1 := by
  cases K <;> rfl

lemma SKind.kind_loc {H d u : ℕ} (K : SKind M) : (K.loc H d u).kind = K := by
  cases K <;> rfl

/-- Enumerating `16 R^2 C^3` numbers by digits below `C, R, C, C, R` and a tag below `16`. -/
lemma flatMap_range_digits {β : Type} (R C : ℕ) (F : ℕ → List β) :
    (List.range (16 * (R * (C * (C * (R * C)))))).flatMap F =
      (List.range C).flatMap fun t5 => (List.range R).flatMap fun t4 =>
      (List.range C).flatMap fun t3 => (List.range C).flatMap fun t2 =>
      (List.range R).flatMap fun t1 => (List.range 16).flatMap fun t =>
        F (pack 16 t (pack R t1 (pack C t2 (pack C t3 (pack R t4 t5))))) := by
  rw [Gn.flatMap_range_mul, Gn.flatMap_range_mul, Gn.flatMap_range_mul, Gn.flatMap_range_mul,
    Gn.flatMap_range_mul]
  rfl

end Lax119563Proofs.Reduction

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp

variable {M : Machine} {s : ℕ}

section Out

variable {x : List Bool} {ρ : List ℕ} {b H : ℕ} {HX RX : Xp} {body : Gn}

lemma getD_stk {l : List ℕ} (hρ : ρ.length = b) (i : ℕ) : (ρ ++ l).getD (b + i) 0 = l.getD i 0 := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  congr 1; omega

lemma rvB_ok (hρ : ρ.length = b) (hH : HX.eval ρ = H) (hHb : HX.Bnd b) (R C : ℕ)
    (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (l : List ℕ) :
    (rvB b HX).Ok H (stkT ρ H R C t ++ l) t.2.1 t.2.2.2.2.1 := by
  have e : ∀ i, (stkT ρ H R C t ++ l).getD (b + i) 0 =
      ([C, t.2.2.2.2.2, R, t.2.2.2.2.1, C, t.2.2.2.1, C, t.2.2.1, R, t.2.1,
      t.2.1 - 1, t.2.2.2.2.1 - 1, H - (t.2.1 + 1), H + 2 - t.2.1,
      pack R t.2.1 (pack C t.2.2.1 (pack C t.2.2.2.1 (pack R t.2.2.2.2.1 t.2.2.2.2.2)))] ++
        l).getD i 0 := fun i => by
    rw [stkT, List.append_assoc, getD_stk hρ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp only [rvB, Xp.eval_var, e]; rfl)
    | (simp only [rvB]; rw [stkT, List.append_assoc]; exact (Xp.eval_append hρ _ hHb).trans hH)
    | (simp only [rvB, Xp.eval_var, e, List.cons_append, List.getD_cons_succ,
        List.getD_cons_zero]; omega)

lemma allB_map {α : Type} {n : ℕ} {l : List α} {f : α → SMv M s} (h : ∀ a ∈ l, (f a).Bnd n) :
    ∀ m ∈ l.map f, m.Bnd n := by
  intro m hm; obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm; exact h a ha

lemma allB_flatMap {α : Type} {n : ℕ} {l : List α} {f : α → List (SMv M s)}
    (h : ∀ a ∈ l, ∀ m ∈ f a, m.Bnd n) : ∀ m ∈ l.flatMap f, m.Bnd n := by
  intro m hm; obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp hm; exact h a ha m hm

lemma allB_cons {n : ℕ} {m₀ : SMv M s} {l : List (SMv M s)} (h₀ : m₀.Bnd n)
    (h : ∀ m ∈ l, m.Bnd n) : ∀ m ∈ m₀ :: l, m.Bnd n := by
  intro m hm; rcases List.mem_cons.mp hm with rfl | hm
  · exact h₀
  · exact h m hm

lemma allB_nil {n : ℕ} : ∀ m ∈ ([] : List (SMv M s)), m.Bnd n := by simp

lemma allBr_cons {n : ℕ} {c : Xp} {l : List (SMv M s)} {rest : List (Xp × List (SMv M s))}
    (h₀ : c.Bnd n ∧ ∀ m ∈ l, m.Bnd n) (h : ∀ br ∈ rest, br.1.Bnd n ∧ ∀ m ∈ br.2, m.Bnd n) :
    ∀ br ∈ (c, l) :: rest, br.1.Bnd n ∧ ∀ m ∈ br.2, m.Bnd n := by
  intro br hbr; rcases List.mem_cons.mp hbr with rfl | hbr
  · exact h₀
  · exact h br hbr

lemma allBr_nil {n : ℕ} :
    ∀ br ∈ ([] : List (Xp × List (SMv M s))), br.1.Bnd n ∧ ∀ m ∈ br.2, m.Bnd n := by simp

/-- The branches read only levels below `n`. -/
lemma SKind.bnd_brs {n : ℕ} {V : RVals} (hV : V.Bnd n) (K : SKind M) :
    ∀ br ∈ K.brs (s := s) V, br.1.Bnd n ∧ ∀ m ∈ br.2, m.Bnd n := by
  have b1 := hV.d; have b2 := hV.u; have b3 := hV.dm1; have b4 := hV.um1; have b5 := hV.hd1
  have b6 := hV.hd2; have b7 := hV.H
  cases K <;> simp only [SKind.brs] <;> (try split_ifs) <;>
    repeat' (first | exact allBr_nil | refine allBr_cons ⟨?_, ?_⟩ ?_ | exact allB_nil |
      (refine allB_flatMap ?_; intro _ _) | (refine allB_map ?_; intro _ _) |
      refine allB_cons ?_ ?_)
  all_goals (try split_ifs) <;> (try simp only [SMv.Bnd, SMv.goto, SMv.fork']) <;>
    (try simp only [SLoc.Bnd]) <;> (try simp only [Xp.Bnd, Xp.eq, Xp.and]) <;>
    (try simp only [b1, b2, b3, b4, b5, b6, b7, and_self, and_true, true_and]) <;>
    (try trivial) <;> (try exact ⟨trivial, trivial⟩)

/-- **The records describe the commands.** -/
theorem desc_recsOf (hρ : ρ.length = b) (hHb : HX.Bnd b) (hRb : RX.Bnd b)
    (hH : HX.eval ρ = H) (hR : RX.eval ρ = radix M H) (ℓ : ℕ) (L : Loc M H) :
    ∃ rs : List (List ℕ), recsOf M s b HX RX x ρ H L = rs.zipIdx.map (fun p => p.2 :: p.1) ∧
      List.Forall₂ (fun mv r => CmdDesc M x s ℓ H (Move.toACmd ℓ L mv) r)
        (moves M x s ℓ H L) rs := by
  set σ := stkL M ρ H L with hσ
  have hV : (rvB b HX).Ok H σ L.tuple.2.1 L.tuple.2.2.2.2.1 := rvB_ok hρ hH hHb _ _ _ _
  have hRσ : RX.eval σ = radix M H := by
    rw [hσ, stkL, stkT, List.append_assoc]; exact (Xp.eval_append hρ _ hRb).trans hR
  obtain ⟨-, hval, hloc⟩ := L.kind_spec
  have hmv := moves_eq (s := s) (x := x) (ℓ := ℓ) hV L.kind hval
  rw [hloc] at hmv
  have hHσ : HX.eval σ = H := by
    rw [hσ, stkL, stkT, List.append_assoc]; exact (Xp.eval_append hρ _ hHb).trans hH
  refine ⟨(selBr σ (L.kind.brs (s := s) (rvB b HX))).map fun m => (m.recX RX HX).map
    fun e => e.eval σ, ?_, ?_⟩
  · rw [recsOf, List.zipIdx_map, List.map_map]
    rfl
  · rw [← hmv, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun m _ => SMv.desc hRσ hHσ L m

end Out

end Lax119563Proofs.Reduction

end Reduction_CmdEnum

/-! ### Formerly `Lax119563Proofs.Reduction.CostCmd` -/

section Reduction_CostCmd

/-!
# Fits and cost of the command generators

* `LinX Γ a`: `a` is linear (`P 0 1`) and reads only the levels of `Γ`; `TyB Γ a τ` likewise for
  a class `τ`.
* `SLoc.codeX_tyB`: location numbers are `P 0 5` (two digits of a linear radix and three
  of a constant one, so in fact `P 0 3`), given linear
  runtime fields (`SLoc.Ok`); `SMv.recX_tyB`: the eight numbers of a move have the classes
  `recTys` (the mask is `big`); `SKind.brs_ok`: all branches of all kinds are typed.
* `hasCost_firstL`, `hasCost_brGen`: the cost of the generators of `Reduction/CmdEnum`.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Xp Ty Gn

variable {M : Machine} {s : ℕ}

/-- Typed in class `τ` and reading only the levels of `Γ`. -/
def TyB (Γ : List Ty) (a : Xp) (τ : Ty) : Prop := HasTy Γ a τ ∧ a.Bnd Γ.length

/-- Linear and reading only the levels of `Γ`. -/
abbrev LinX (Γ : List Ty) (a : Xp) : Prop := TyB Γ a (P 0 1)

variable {Γ : List Ty}

lemma TyB.le {a : Xp} {τ τ' : Ty} (h : TyB Γ a τ) (hτ : Ty.Le τ τ') : TyB Γ a τ' :=
  ⟨h.1.le hτ, h.2⟩

lemma TyB.weaken {a : Xp} {τ : Ty} (h : TyB Γ a τ) (us : List Ty) : TyB (Γ ++ us) a τ :=
  ⟨h.1.weaken h.2 us, Xp.Bnd.mono (by simp) h.2⟩

lemma tyB_const (c : ℕ) : TyB Γ (const c) (P 0 0) := ⟨hasTy_const c, trivial⟩

lemma linX_const (c : ℕ) : LinX Γ (const c) := (tyB_const c).le ⟨le_rfl, by omega⟩

lemma tyB_var {j : ℕ} {τ : Ty} (us : List Ty) (h : us.getD j (P 0 0) = τ) (hj : j < us.length) :
    TyB (Γ ++ us) (var (Γ.length + j)) τ := by
  refine ⟨hasTy_var' ?_, show Γ.length + j < (Γ ++ us).length by simp; omega⟩
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simpa using h

lemma linX_add_const {a : Xp} (h : LinX Γ a) (c : ℕ) : LinX Γ (add a (const c)) :=
  ⟨hasTy_add h.1 (linX_const c).1, h.2, trivial⟩

lemma linX_add {a b : Xp} (ha : LinX Γ a) (hb : LinX Γ b) : LinX Γ (add a b) :=
  ⟨hasTy_add ha.1 hb.1, ha.2, hb.2⟩

lemma tyB_lt {a b : Xp} {τa τb : Ty} (ha : TyB Γ a τa) (hb : TyB Γ b τb) :
    TyB Γ (Xp.lt a b) (P 0 0) := ⟨hasTy_lt ha.1 hb.1, ha.2, hb.2⟩

lemma tyB_eq {a b : Xp} {τa τb : Ty} (ha : TyB Γ a τa) (hb : TyB Γ b τb) :
    TyB Γ (Xp.eq a b) (P 0 0) :=
  ⟨hasTy_eq ha.1 hb.1, ⟨⟨⟨ha.2, hb.2⟩, ⟨hb.2, ha.2⟩⟩, trivial⟩⟩

lemma tyB_and {a b : Xp} {τa τb : Ty} (ha : TyB Γ a τa) (hb : TyB Γ b τb) :
    TyB Γ (Xp.and a b) (P 0 0) := ⟨hasTy_and ha.1 hb.1, trivial, ha.2, hb.2⟩

lemma tyB_not {a : Xp} {τ : Ty} (ha : TyB Γ a τ) : TyB Γ (Xp.not a) (P 0 0) :=
  ⟨hasTy_not ha.1, ha.2, trivial⟩

lemma tyB_mulC {a : Xp} {e d : ℕ} (ha : TyB Γ a (P e d)) (c : ℕ) : TyB Γ (mulC c a) (P e d) :=
  ⟨hasTy_mulC ha.1 c, Xp.bnd_mulC ha.2 c⟩

/-- `a + b R` with `a, R` linear and `b` of degree `d`. -/
lemma tyB_horner {a b R : Xp} {d : ℕ} (ha : LinX Γ a) (hb : TyB Γ b (P 0 d)) (hR : LinX Γ R)
    (hd : 1 ≤ d) : TyB Γ (add a (mul b R)) (P 0 (d + 1)) := by
  have hm : HasTy Γ (mul b R) (P 0 (d + 1)) := by
    simpa using hasTy_mul hb.1 hR.1 hR.1
  exact ⟨hasTy_add (ha.1.le ⟨le_rfl, by omega⟩) hm, ha.2, Xp.bnd_mul hb.2 hR.2⟩

/-- `a + c b` with `a` linear, `b` of degree `d ≥ 1` and a constant `c`. -/
lemma tyB_hornerC {a b : Xp} {d : ℕ} (ha : LinX Γ a) (hb : TyB Γ b (P 0 d)) (c : ℕ)
    (hd : 1 ≤ d) : TyB Γ (add a (mulC c b)) (P 0 d) :=
  ⟨hasTy_add (ha.1.le ⟨le_rfl, hd⟩) (tyB_mulC hb c).1, ha.2, (tyB_mulC hb c).2⟩

lemma linX_minX {a h : Xp} (ha : LinX Γ a) (hh : LinX Γ h) : LinX Γ (minX a h) := by
  have hc : TyB Γ (Xp.lt a (add h (const 1))) (P 0 0) := tyB_lt ha (linX_add_const hh 1)
  have hc' : TyB Γ (Xp.not (Xp.lt a (add h (const 1)))) (P 0 0) := tyB_not hc
  have m1 : HasTy Γ (mul a (Xp.lt a (add h (const 1)))) (P 0 1) := by
    simpa using hasTy_mul ha.1 hc.1 (hc.1.le ⟨le_rfl, by omega⟩)
  have m2 : HasTy Γ (mul h (Xp.not (Xp.lt a (add h (const 1))))) (P 0 1) := by
    simpa using hasTy_mul hh.1 hc'.1 (hc'.1.le ⟨le_rfl, by omega⟩)
  exact ⟨hasTy_add m1 m2, bnd_minX ha.2 hh.2⟩

/-! ## Locations and moves -/

namespace SLoc

/-- The runtime fields are linear. -/
def Ok (Γ : List Ty) : SLoc M → Prop
  | cell d .. => LinX Γ d
  | state d .. => LinX Γ d
  | headIn d _ _ u => LinX Γ d ∧ LinX Γ u
  | headSet d .. => LinX Γ d
  | restore d .. => LinX Γ d
  | gather d .. => LinX Γ d
  | _ => True

lemma flds_lin {HX : Xp} (hH : LinX Γ HX) {L : SLoc M} (h : L.Ok Γ) :
    LinX Γ (L.flds HX).1 ∧ LinX Γ (L.flds HX).2.1 ∧ LinX Γ (L.flds HX).2.2.1 ∧
      LinX Γ (L.flds HX).2.2.2.1 ∧ LinX Γ (L.flds HX).2.2.2.2 := by
  cases L <;> simp only [flds] <;>
    first
    | exact ⟨linX_const _, linX_const _, linX_const _, linX_const _, linX_const _⟩
    | exact ⟨linX_minX h hH, linX_const _, linX_const _, linX_const _, linX_const _⟩
    | exact ⟨linX_minX h.1 hH, linX_const _, linX_const _, linX_minX h.2 hH, linX_const _⟩

lemma codeX_tyB {R HX : Xp} (hR : LinX Γ R) (hH : LinX Γ HX) {L : SLoc M} (h : L.Ok Γ) :
    TyB Γ (L.codeX R HX) (P 0 5) := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := flds_lin hH h
  have t4 := tyB_horner f4 f5 hR le_rfl
  have t3 := tyB_hornerC f3 t4 (cM M) (by omega)
  have t2 := tyB_hornerC f2 t3 (cM M) (by omega)
  have t1 := (tyB_horner f1 t2 hR (by omega)).le (show Ty.Le (P 0 3) (P 0 5) from ⟨le_rfl, by omega⟩)
  have := tyB_mulC t1 16
  exact ⟨hasTy_add ((hasTy_const _).le ⟨le_rfl, by omega⟩) this.1, trivial, this.2⟩

end SLoc

namespace SMv

/-- The iteration counts and the locations are linear. -/
def Ok (Γ : List Ty) : SMv M s → Prop
  | step k _ _ _ dst => LinX Γ k ∧ dst.Ok Γ
  | fork k _ _ l r => LinX Γ k ∧ l.Ok Γ ∧ r.Ok Γ
  | hit _ _ dst => dst.Ok Γ
  | miss _ dst => dst.Ok Γ

end SMv

/-- The classes of the eight numbers of a move. -/
def recTys : List Ty := [P 0 0, .big, P 0 5, P 0 5, P 0 0, P 0 1, P 0 0, P 0 0]

namespace SMv

lemma recX_tyB {R HX : Xp} (hR : LinX Γ R) (hH : LinX Γ HX) {m : SMv M s} (h : m.Ok Γ) :
    List.Forall₂ (fun a τ => TyB Γ a τ) (m.recX R HX) recTys := by
  have c0 : ∀ c, TyB Γ (const c) (P 0 0) := fun c => tyB_const c
  have c5 : ∀ c, TyB Γ (const c) (P 0 5) := fun c => (tyB_const c).le ⟨le_rfl, by omega⟩
  have c1 : ∀ c, TyB Γ (const c) (P 0 1) := fun c => linX_const c
  cases m with
  | step k m q v dst =>
    simp only [recX, recTys]
    exact .cons (c0 _) (.cons ⟨hasTy_shl (hasTy_const _) h.1.1, trivial, h.1.2⟩
      (.cons (SLoc.codeX_tyB hR hH h.2) (.cons (c5 _) (.cons (c0 _) (.cons h.1
        (.cons (c0 _) (.cons (c0 _) .nil)))))))
  | fork k m q l r =>
    simp only [recX, recTys]
    exact .cons (c0 _) (.cons ((tyB_const _).le (Ty.le_big _))
      (.cons (SLoc.codeX_tyB hR hH h.2.1) (.cons (SLoc.codeX_tyB hR hH h.2.2) (.cons (c0 _)
        (.cons h.1 (.cons (c0 _) (.cons (c0 _) .nil)))))))
  | hit ν c dst =>
    simp only [recX, recTys]
    exact .cons (c0 _) (.cons ((tyB_const _).le (Ty.le_big _))
      (.cons (SLoc.codeX_tyB hR hH h) (.cons (c5 _) (.cons (c0 _)
        (.cons (c1 _) (.cons (c0 _) (.cons (c0 _) .nil)))))))
  | miss i dst =>
    simp only [recX, recTys]
    exact .cons (c0 _) (.cons ((tyB_const _).le (Ty.le_big _))
      (.cons (SLoc.codeX_tyB hR hH h) (.cons (c5 _) (.cons (c0 _)
        (.cons (c1 _) (.cons (c0 _) (.cons (c0 _) .nil)))))))

end SMv

/-- The runtime values are linear. -/
structure RVals.Lin (Γ : List Ty) (V : RVals) : Prop where
  d : LinX Γ V.d
  u : LinX Γ V.u
  dm1 : LinX Γ V.dm1
  um1 : LinX Γ V.um1
  hd1 : LinX Γ V.hd1
  hd2 : LinX Γ V.hd2
  H : LinX Γ V.H

lemma SKind.brs_ok {V : RVals} (hV : V.Lin Γ) (K : SKind M) :
    ∀ br ∈ K.brs (s := s) V, TyB Γ br.1 (P 0 0) ∧ ∀ m ∈ br.2, SMv.Ok Γ m := by
  have c1 : TyB Γ (const 1) (P 0 0) := tyB_const 1
  have L0 : LinX Γ (const 0) := linX_const 0
  have Ld1 : LinX Γ (add V.d (const 1)) := linX_add_const hV.d 1
  have Lh2 : LinX Γ (add V.hd1 (const 2)) := linX_add_const hV.hd1 2
  cases K with
  | accept => simp [SKind.brs]
  | reject => simp [SKind.brs]
  | query =>
    simp only [SKind.brs, List.mem_singleton]
    rintro br rfl
    refine ⟨c1, fun m hm => ?_⟩
    simp only [List.mem_map] at hm
    obtain ⟨p, -, rfl⟩ := hm
    exact ⟨L0, L0⟩
  | cell θ ν c =>
    simp only [SKind.brs]
    by_cases hθ : θ.val = 0
    · rw [if_pos hθ]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro br (rfl | rfl)
      · refine ⟨tyB_eq hV.d (tyB_const 0), fun m hm => ?_⟩
        simp only [List.mem_cons] at hm
        rcases hm with rfl | hm
        · trivial
        · by_cases hc : c = (0, false)
          · rw [if_pos hc] at hm
            simp only [List.mem_map] at hm
            obtain ⟨i, -, rfl⟩ := hm
            trivial
          · rw [if_neg hc] at hm; simp at hm
      · refine ⟨c1, fun m hm => ?_⟩
        simp only [List.mem_flatMap, List.mem_map] at hm
        obtain ⟨θ', -, β, -, rfl⟩ := hm
        exact ⟨hV.hd2, hV.dm1, hV.dm1⟩
    · rw [if_neg hθ]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro br (rfl | rfl)
      · refine ⟨tyB_lt hV.d hV.H, fun m hm => ?_⟩
        simp only [List.mem_map] at hm
        obtain ⟨β, -, rfl⟩ := hm
        exact ⟨L0, hV.d, hV.d⟩
      · refine ⟨c1, fun m hm => ?_⟩
        by_cases h2 : θ.val = 2
        · rw [if_pos h2] at hm
          simp only [List.mem_flatMap, List.mem_map] at hm
          obtain ⟨_, -, _, -, jj, -, rfl⟩ := hm
          exact ⟨L0, trivial⟩
        · rw [if_neg h2] at hm; simp at hm
  | state θ p =>
    simp only [SKind.brs]
    by_cases hθ : θ.val = 0
    · rw [if_pos hθ]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro br (rfl | rfl)
      · refine ⟨tyB_eq hV.d (tyB_const 0), fun m hm => ?_⟩
        by_cases hp : p = (0, none)
        · rw [if_pos hp] at hm
          simp only [List.mem_singleton] at hm; subst hm; exact ⟨L0, trivial⟩
        · rw [if_neg hp] at hm; simp at hm
      · refine ⟨c1, fun m hm => ?_⟩
        simp only [List.mem_map] at hm
        obtain ⟨θ', -, rfl⟩ := hm
        exact ⟨hV.hd2, hV.dm1⟩
    · rw [if_neg hθ]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro br (rfl | rfl)
      · refine ⟨tyB_lt hV.d hV.H, fun m hm => ?_⟩
        simp only [List.mem_map] at hm
        obtain ⟨e, -, rfl⟩ := hm
        exact ⟨Lh2, Ld1⟩
      · refine ⟨c1, fun m hm => ?_⟩
        by_cases h2 : θ.val = 2
        · rw [if_pos h2] at hm
          simp only [List.mem_map] at hm
          obtain ⟨_, -, rfl⟩ := hm
          exact ⟨L0, trivial⟩
        · rw [if_neg h2] at hm; simp at hm
  | headIn θ ν =>
    simp only [SKind.brs, List.mem_cons, List.not_mem_nil, or_false]
    rintro br (rfl | rfl)
    · refine ⟨tyB_and (tyB_lt (linX_add hV.u hV.d) hV.H) (tyB_eq hV.u (tyB_const 0)),
        fun m hm => ?_⟩
      simp only [List.mem_map] at hm
      obtain ⟨γ, -, rfl⟩ := hm
      exact ⟨L0, hV.d⟩
    · refine ⟨tyB_lt (linX_add hV.u hV.d) hV.H, fun m hm => ?_⟩
      simp only [List.mem_flatMap, List.mem_map] at hm
      obtain ⟨e, -, e', -, rfl⟩ := hm
      exact ⟨hV.um1, hV.d, hV.um1⟩
  | headSet θ ν β =>
    simp only [SKind.brs, List.mem_singleton]
    rintro br rfl
    refine ⟨tyB_lt hV.d hV.H, fun m hm => ?_⟩
    simp only [List.mem_map] at hm
    obtain ⟨q, -, rfl⟩ := hm
    exact ⟨hV.hd1, hV.d, hV.hd1⟩
  | restore θ ν c β =>
    simp only [SKind.brs, List.mem_singleton]
    rintro br rfl
    refine ⟨tyB_lt hV.d hV.H, fun m hm => ?_⟩
    simp only [List.mem_map] at hm
    obtain ⟨q, -, rfl⟩ := hm
    split_ifs
    · exact ⟨hV.hd1, Ld1⟩
    · exact ⟨hV.hd1, hV.d⟩
  | gather θ ν c β =>
    simp only [SKind.brs, List.mem_singleton]
    rintro br rfl
    refine ⟨tyB_lt hV.d hV.H, fun m hm => ?_⟩
    simp only [List.mem_map] at hm
    obtain ⟨q, -, rfl⟩ := hm
    exact ⟨hV.hd1, hV.d⟩
  | baseCell ν ρ old k =>
    simp only [SKind.brs, List.mem_singleton]
    rintro br rfl
    refine ⟨c1, fun m hm => ?_⟩
    split_ifs at hm
    · simp only [List.mem_singleton] at hm; subst hm; exact ⟨L0, trivial, trivial⟩
    · simp only [List.mem_singleton] at hm; subst hm; exact ⟨L0, hV.H, hV.H⟩
  | baseState ρ k =>
    simp only [SKind.brs, List.mem_singleton]
    rintro br rfl
    refine ⟨c1, fun m hm => ?_⟩
    split_ifs at hm
    · simp only [List.mem_singleton] at hm; subst hm; exact ⟨L0, trivial, trivial⟩
    · simp only [List.mem_singleton] at hm; subst hm; exact ⟨L0, hV.H⟩
  | setJ ν h c =>
    simp only [SKind.brs, List.mem_singleton]
    rintro br rfl
    refine ⟨c1, fun m hm => ?_⟩
    simp only [List.mem_map] at hm
    obtain ⟨q, -, rfl⟩ := hm
    exact ⟨L0, hV.H⟩


lemma SKind.sloc_ok {d u : Xp} (hd : LinX Γ d) (hu : LinX Γ u) (K : SKind M) :
    (K.sloc d u).Ok Γ := by
  cases K
  all_goals first | trivial | exact hd | exact ⟨hd, hu⟩

/-! ## The enumerator -/

namespace Gn

lemma hasCost_firstL {α : Type} {c : α → Xp} {f : α → Gn} {e d : ℕ} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ τ, HasTy Γ (c a) τ) → (∀ a ∈ l, HasCost Γ (f a) e d) →
      HasCost Γ (firstL c f l) e d
  | [], _, _ => hasCost_skip.mono (Nat.zero_le _) (Nat.zero_le _)
  | a :: l, hc, hf => by
    obtain ⟨τ, hτ⟩ := hc a (by simp)
    exact hasCost_ite hτ (hf a (by simp))
      (hasCost_firstL (fun a' ha' => hc a' (by simp [ha'])) fun a' ha' => hf a' (by simp [ha']))

lemma hasCost_brGen {RX HX : Xp} (hR : LinX Γ RX) (hH : LinX Γ HX) {body : Gn} {e d : ℕ}
    (hbody : HasCost (Γ ++ P 0 0 :: recTys) body e d) :
    ∀ brs : List (Xp × List (SMv M s)),
      (∀ br ∈ brs, TyB Γ br.1 (P 0 0) ∧ ∀ m ∈ br.2, SMv.Ok Γ m) →
      HasCost Γ (brGen RX HX body brs) e d
  | [], _ => hasCost_skip.mono (Nat.zero_le _) (Nat.zero_le _)
  | (c, ms) :: rest, h => by
    have h0 := h (c, ms) (by simp)
    refine hasCost_ite h0.1.1 (hasCost_seqL fun g hg => ?_)
      (hasCost_brGen hR hH hbody rest fun br hbr => h br (by simp [hbr]))
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
    have hm : p.1 ∈ ms := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hp)
    have hT : TyL (Γ ++ []) (const p.2 :: p.1.recX RX HX) (P 0 0 :: recTys) :=
      tyL_of_forall₂ (.cons (tyB_const p.2) (SMv.recX_tyB hR hH (h0.2 _ hm))) []
    exact hasCost_bindL (by simpa using hT) hbody

end Gn

lemma hasCost_loop' {τs l : List Ty} {lim : Xp} {g : Gn} {e₀ d₀ e d : ℕ}
    (hl : HasTy (τs ++ l) lim (P e₀ d₀)) (hg : HasCost (τs ++ (l ++ [P e₀ d₀, P e₀ d₀])) g e d) :
    HasCost (τs ++ l) (Gn.loop lim g) (e₀ + e) (d₀ + d) :=
  hasCost_loop hl (by rwa [List.append_assoc])

end Lax119563Proofs.Reduction

end Reduction_CostCmd

/-! ### Formerly `Lax119563Proofs.Reduction.SchEnum` -/

section Reduction_SchEnum

/-!
# Keys of the command records

`keys_pairwise`: the keys `(location number, move index)` of the command records strictly
increase (lexicographically, `lexLt`), so the index of a command in the code-ordered command
list is the number of records with a smaller key, which a generator computes with `Gn.count`.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp

variable {M : Machine} {s : ℕ}

lemma pairwise_zipIdx_snd {β : Type} (l : List β) (k : ℕ) :
    (l.zipIdx k).Pairwise (fun a b => a.2 < b.2) := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    rw [List.zipIdx_cons, List.pairwise_cons]
    refine ⟨fun p hp => ?_, ih (k + 1)⟩
    have := List.le_snd_of_mem_zipIdx hp
    simp only
    omega

/-- The keys of all records, in enumeration order. -/
noncomputable def recKeys (M : Machine) (s b : ℕ) (HX RX : Xp) (x : List Bool) (ρ : List ℕ)
    (H : ℕ) : List (ℕ × ℕ) :=
  (List.range (numLoc M H)).flatMap fun c =>
    match decodeLoc M H c with
    | some L => (recsOf M s b HX RX x ρ H L).map fun r => ((Loc.code L).val, r.headD 0)
    | none => []

lemma keys_pairwise {b : ℕ} {HX RX : Xp} {x : List Bool} {ρ : List ℕ} {H : ℕ} (hρ : ρ.length = b)
    (hHb : HX.Bnd b) (hRb : RX.Bnd b) (hH : HX.eval ρ = H) (hR : RX.eval ρ = radix M H) :
    (recKeys M s b HX RX x ρ H).Pairwise (fun p q => lexLt p q = true) := by
  have block : ∀ L : Loc M H, ((recsOf M s b HX RX x ρ H L).map fun r =>
      ((Loc.code L).val, r.headD 0)).Pairwise (fun p q => lexLt p q = true) := fun L => by
    obtain ⟨rs, hrs, -⟩ := desc_recsOf (s := s) (x := x) hρ hHb hRb hH hR 0 L
    rw [hrs, List.map_map, List.pairwise_map]
    refine (pairwise_zipIdx_snd rs 0).imp fun h => ?_
    simp only [Function.comp, List.headD_cons, lexLt, decide_eq_true_eq]
    exact Or.inr ⟨trivial, h⟩
  unfold recKeys
  rw [List.pairwise_flatMap]
  refine ⟨fun c _ => ?_, ?_⟩
  · cases decodeLoc M H c with
    | none => exact List.Pairwise.nil
    | some L => exact block L
  · refine (List.pairwise_lt_range (n := numLoc M H)).imp fun {c c'} hcc' => ?_
    intro p hp q hq
    cases hd : decodeLoc M H c with
    | none => rw [hd] at hp; simp at hp
    | some L =>
      cases hd' : decodeLoc M H c' with
      | none => rw [hd'] at hq; simp at hq
      | some L' =>
        rw [hd] at hp; rw [hd'] at hq
        obtain ⟨r, -, rfl⟩ := List.mem_map.mp hp
        obtain ⟨r', -, rfl⟩ := List.mem_map.mp hq
        simp only [lexLt, decide_eq_true_eq, code_of_decodeLoc hd, code_of_decodeLoc hd']
        omega

end Lax119563Proofs.Reduction

end Reduction_SchEnum

/-! ### Formerly `Lax119563Proofs.Reduction.CmdStk` -/

section Reduction_CmdStk

/-!
# The stacks of the commands

`cmdStks`: the stacks of the commands of the code-ordered verifier program, one per command,
in order. They correspond to the commands of `verifierCmds'` (relation `StkCmd`: length
`b + 25`, prefix `ρ`, source number at level `b + 15`, `CmdDesc` of the levels from `b + 17`
on; `block_desc`), and their keys (levels `b + 15, b + 16`) are the list `keyList`
(independent of `b` and `ρ`), which strictly increases (`keyList_pairwise`). `beforeX b b'`
compares the key of a stack with the key of an outer stack (`eval_beforeX`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp

variable {M : Machine} {s : ℕ}

section Defs

variable (M s)

/-- The stacks on which the body of the command enumerator runs, in order. -/
noncomputable def cmdStks (b : ℕ) (HX RX : Xp) (x : List Bool) (ρ : List ℕ) (H : ℕ) :
    List (List ℕ) :=
  (List.range (numLoc M H)).flatMap fun c =>
    match decodeLoc M H c with
    | some L => (recsOf M s b HX RX x ρ H L).map (stkL M ρ H L ++ ·)
    | none => []

/-- The keys `(location number, move index)` of the commands. -/
noncomputable def keyList (x : List Bool) (ℓ H : ℕ) : List (ℕ × ℕ) :=
  (List.range (numLoc M H)).flatMap fun c =>
    match decodeLoc M H c with
    | some L => (List.range (moves M x s ℓ H L).length).map ((Loc.code L).val, ·)
    | none => []

end Defs

/-- The key of a stack of the enumerator at base `b`. -/
def keyAt (b : ℕ) (τ : List ℕ) : ℕ × ℕ := (τ.getD (b + 15) 0, τ.getD (b + 16) 0)

lemma CmdDesc.length {x : List Bool} {ℓ H : ℕ} {cmd : ACmd (Loc M H) s} {r : List ℕ}
    (h : CmdDesc M x s ℓ H cmd r) : r.length = 8 := by
  cases cmd <;> exact h.1

lemma src_toACmd {L : Type} {ℓ : ℕ} (src : L) (mv : Move L s) : (mv.toACmd ℓ src).src = src := by
  cases mv <;> rfl

lemma map_zipIdx_snd {α β : Type} (f : ℕ → β) :
    ∀ (l : List α) (k : ℕ), (l.zipIdx k).map (fun p => f p.2) = (List.range' k l.length).map f
  | [], _ => rfl
  | a :: l, k => by
    rw [List.zipIdx_cons, List.map_cons, map_zipIdx_snd f l (k + 1)]
    simp [List.range'_succ]

lemma sum_map_ite_filter {α : Type} (p : α → Bool) (f : α → ℕ) (l : List α) :
    (l.map fun a => if p a then f a else 0).sum = ((l.filter p).map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a <;> simp [List.filter_cons, h, ih]

/-- With strictly increasing keys, the entries with a key below that of entry `i` are the
first `i` entries. -/
lemma filter_lexLt_eq_take {α : Type} (key : α → ℕ × ℕ) :
    ∀ (l : List α), l.Pairwise (fun a b => lexLt (key a) (key b) = true) →
      ∀ (i : ℕ) (hi : i < l.length),
        l.filter (fun a => lexLt (key a) (key l[i])) = l.take i
  | [], _, i, hi => by simp at hi
  | a :: l, h, i, hi => by
    rw [List.pairwise_cons] at h
    rcases i with _ | i
    · simp only [List.getElem_cons_zero, List.filter_cons, lexLt_irrefl, Bool.false_eq_true,
        if_false, List.take_zero]
      rw [List.filter_eq_nil_iff]
      intro b hb hlt
      rw [lexLt_asymm (h.1 b hb)] at hlt
      exact absurd hlt (by simp)
    · have hi' : i < l.length := by simpa using hi
      simp only [List.getElem_cons_succ, List.filter_cons, List.take_succ_cons]
      rw [if_pos (h.1 _ (List.getElem_mem hi')), filter_lexLt_eq_take key l h.2 i hi']

lemma forall₂_exists_of_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ {a : α}, a ∈ l → ∃ b ∈ l', R a b
  | [], [], List.Forall₂.nil, _, h => by simp at h
  | _ :: _, _ :: _, List.Forall₂.cons h t, _, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨b, hb, hr⟩ := forall₂_exists_of_mem_left t ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

lemma getD_take' {l : List ℕ} {i n : ℕ} (h : i < n) : (l.take n).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]

section Stacks

variable {x : List Bool} {ρ : List ℕ} {b H : ℕ} {HX RX : Xp}

lemma length_stkL (hρ : ρ.length = b) (L : Loc M H) : (stkL M ρ H L).length = b + 16 := by
  simp [stkL, stkT, hρ]

lemma getD_stkL_code (hρ : ρ.length = b) (L : Loc M H) (l : List ℕ) :
    (stkL M ρ H L ++ l).getD (b + 15) 0 = (Loc.code L).val := by
  rw [List.getD_append _ _ _ _ (by rw [length_stkL hρ]; omega)]
  simp [stkL, stkT, List.getD_append_right, hρ]

lemma getD_stkL_succ (hρ : ρ.length = b) (L : Loc M H) (k : ℕ) (r : List ℕ) (i : ℕ) :
    (stkL M ρ H L ++ k :: r).getD (b + 16 + i) 0 = (k :: r).getD i 0 := by
  rw [List.getD_append_right _ _ _ _ (by rw [length_stkL hρ]; omega), length_stkL hρ]
  congr 1; omega

lemma getD_stkL_head (hρ : ρ.length = b) (L : Loc M H) (r : List ℕ) :
    (stkL M ρ H L ++ r).getD (b + 16) 0 = r.headD 0 := by
  rw [List.getD_append_right _ _ _ _ (by rw [length_stkL hρ]), length_stkL hρ]
  cases r <;> simp

variable (hρ : ρ.length = b) (hHb : HX.Bnd b) (hRb : RX.Bnd b) (hH : HX.eval ρ = H)
  (hR : RX.eval ρ = radix M H)
include hρ hHb hRb hH hR

/-- The stack `τ` of the enumerator belongs to the command `cmd`. -/
def StkCmd (x : List Bool) (s ℓ H b : ℕ) (ρ : List ℕ) (τ : List ℕ) (cmd : ACmd (Loc M H) s) :
    Prop :=
  τ.length = b + 25 ∧ τ.take b = ρ ∧ τ.getD (b + 15) 0 = (Loc.code cmd.src).val ∧
    CmdDesc M x s ℓ H cmd (τ.drop (b + 17))

omit hR in
lemma block_desc (hR : RX.eval ρ = radix M H) (ℓ : ℕ) (L : Loc M H) :
    ∃ rs : List (List ℕ), recsOf M s b HX RX x ρ H L = rs.zipIdx.map (fun p => p.2 :: p.1) ∧
      List.Forall₂ (fun mv r => CmdDesc M x s ℓ H (Move.toACmd ℓ L mv) r)
        (moves M x s ℓ H L) rs :=
  desc_recsOf hρ hHb hRb hH hR ℓ L

/-- **The keys of the stacks.** -/
theorem keys_cmdStks (ℓ : ℕ) :
    (cmdStks M s b HX RX x ρ H).map (keyAt b) = keyList M s x ℓ H := by
  rw [cmdStks, keyList, List.map_flatMap]
  refine List.flatMap_congr fun c _ => ?_
  cases decodeLoc M H c with
  | none => rfl
  | some L =>
    simp only
    obtain ⟨rs, hrs, hF⟩ := block_desc hρ hHb hRb hH hR ℓ L
    rw [hrs, List.map_map, List.map_map, hF.length_eq, List.range_eq_range']
    rw [← map_zipIdx_snd (fun k => ((Loc.code L).val, k)) rs 0]
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp, keyAt, getD_stkL_code hρ]
    congr 1
    have := getD_stkL_succ hρ L p.2 p.1 0
    simpa using this

theorem keyList_pairwise (ℓ : ℕ) :
    (keyList M s x ℓ H).Pairwise (fun p q => lexLt p q = true) := by
  have hk : recKeys M s b HX RX x ρ H = (cmdStks M s b HX RX x ρ H).map (keyAt b) := by
    rw [cmdStks, recKeys, List.map_flatMap]
    refine List.flatMap_congr fun c _ => ?_
    cases decodeLoc M H c with
    | none => rfl
    | some L =>
      simp only [List.map_map]
      refine List.map_congr_left fun r _ => ?_
      simp only [Function.comp, keyAt, getD_stkL_code hρ, getD_stkL_head hρ]
  rw [keys_cmdStks hρ hHb hRb hH hR ℓ] at hk
  rw [← hk]
  exact keys_pairwise hρ hHb hRb hH hR

end Stacks

/-! ## Counting the commands before a given one -/

/-- The key at base `b'` is lexicographically below the key at base `b`. -/
def beforeX (b b' : ℕ) : Xp :=
  or (lt (var (b' + 15)) (var (b + 15)))
    (and (eq (var (b' + 15)) (var (b + 15))) (lt (var (b' + 16)) (var (b + 16))))

lemma eval_beforeX (b b' : ℕ) (τ : List ℕ) :
    (beforeX b b').eval τ = if lexLt (keyAt b' τ) (keyAt b τ) then 1 else 0 := by
  have e1 : (eq (var (b' + 15)) (var (b + 15))).eval τ ≤ 1 := by
    rw [Xp.eval_eq]; split_ifs <;> omega
  have e2 : (lt (var (b' + 16)) (var (b + 16))).eval τ ≤ 1 := by
    rw [Xp.eval_lt_eq]; split_ifs <;> omega
  unfold beforeX
  rw [Xp.eval_or, Xp.eval_and e1 e2]
  simp only [Xp.eval_eq, Xp.eval_lt_eq, Xp.eval_var, keyAt, lexLt]
  by_cases h1 : τ.getD (b' + 15) 0 < τ.getD (b + 15) 0 <;>
    by_cases h2 : τ.getD (b' + 15) 0 = τ.getD (b + 15) 0 <;>
    by_cases h3 : τ.getD (b' + 16) 0 < τ.getD (b + 16) 0 <;>
    simp [h1, h2, h3] <;> omega

variable {x : List Bool} {b H : ℕ} {HX RX : Xp}

end Lax119563Proofs.Reduction

end Reduction_CmdStk
