import Lax119563Proofs.Reduction.SArith

/-!
# Expressions with loop-based operations

`Xp`: expressions over a stack of naturals (`var i` reads level `i`), with constant-time
operations (`add, lt, half, odd`) and loop-based operations whose number of iterations is the
value of their last argument `k`: `mulB a b k = a * (b % 2^k)`, `shl a k = a * 2^k`,
`shr a k = a / 2^k`, `xorM a b k = (a ^^^ b) % 2^k`.

`Xp.comp R d A t e` evaluates `e` into register `t` of `Stm (R + 1)` (register `R` is a sink),
using registers `≥ t` as temporaries; levels `i < d` not in `A` are read from register `i`,
all other levels read as `0`. `Xp.spec`: the compiled statement is `Good` (no output, cost at
most `κ w * cost`), computes the value, and keeps all registers below `t`.

`Stm.good_loopInv`: a loop rule with an invariant (for bodies writing accumulators).
-/

namespace Lax119563Proofs.Reduction

/-! ## Registers -/

/-- Register `t` among `R + 1` registers (`R` is a sink for out-of-range indices). -/
def rg (R t : ℕ) : Fin (R + 1) := ⟨min t R, by omega⟩

lemma rg_ne {R t t' : ℕ} (h : t < R) (hne : t ≠ t') : rg R t ≠ rg R t' := by
  intro e
  have := congrArg Fin.val e
  simp only [rg] at this
  omega

lemma rg_inj {R t t' : ℕ} (h : t < R) (h' : t' < R) : rg R t = rg R t' ↔ t = t' :=
  ⟨fun e => by by_contra hne; exact rg_ne h hne e, fun e => e ▸ rfl⟩

/-- The cost unit. -/
def κ (w : ℕ) : ℕ := 32 * Ex.nodeCost w

lemma unitCost_le_κ (w : ℕ) : unitCost w ≤ Ex.nodeCost w := Ex.unitCost_le_nodeCost w

variable {R : ℕ} {x : List Bool} {w : ℕ}

/-! ## Loops with invariants -/

namespace Stm

lemma good_loopInv {N : ℕ} {i lim : Fin N} {body : Stm N} {env : Fin N → ℕ}
    (Inv : ℕ → (Fin N → ℕ) → Prop) (g : ℕ → List ℕ) (Tb : ℕ)
    (hL : env lim + 1 < 2 ^ w) (h0 : Inv 0 env)
    (hs : ∀ k < env lim, ∀ e, Inv k e →
      Good x w body (Function.update e i k) (g k) Tb ∧
        Inv (k + 1) (exec x body (Function.update e i k)).1) :
    Good x w (loop i lim body) env ((List.range (env lim)).flatMap g)
      (env lim * (Tb + 4 * unitCost w + 1) + 2 * unitCost w + 1) ∧
    Inv (env lim) (runLoop (fun k e => exec x body (Function.update e i k)) (env lim) env).1 := by
  have HI := runLoop_inv (f := fun k e => exec x body (Function.update e i k)) (L := env lim)
    Inv h0 (fun k hk e he => (hs k hk e he).2)
  have H : ∀ k < env lim, Good x w body
      (Function.update (runLoop (fun k e => exec x body (Function.update e i k)) k env).1 i k)
      (g k) Tb := fun k hk => (hs k hk _ (HI k hk.le)).1
  refine ⟨⟨⟨hL, fun k hk => (H k hk).fits⟩, ?_, ?_⟩, HI _ le_rfl⟩
  · simp only [exec]
    rw [runLoop_out]
    refine List.flatMap_congr fun k hk => ?_
    exact (H k (List.mem_range.mp hk)).out_eq
  · simp only [cost]
    have : ∑ k ∈ Finset.range (env lim), (cost x w body (Function.update
        (runLoop (fun k e => exec x body (Function.update e i k)) k env).1 i k) +
          4 * unitCost w + 1) ≤ ∑ k ∈ Finset.range (env lim), (Tb + 4 * unitCost w + 1) :=
      Finset.sum_le_sum fun k hk => by have := (H k (Finset.mem_range.mp hk)).cost_le; omega
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
    omega

lemma good_loopXInv {N : ℕ} {i lim xb : Fin N} {body : Stm N} {env : Fin N → ℕ}
    (Inv : ℕ → (Fin N → ℕ) → Prop) (g : ℕ → List ℕ) (Tb : ℕ)
    (hL : env lim + 1 < 2 ^ w) (h0 : Inv 0 env)
    (hs : ∀ k < env lim, ∀ e, Inv k e →
      Good x w body (Function.update (Function.update e i k) xb (inBit x k)) (g k) Tb ∧
        Inv (k + 1) (exec x body (Function.update (Function.update e i k) xb (inBit x k))).1) :
    Good x w (loopX i lim xb body) env ((List.range (env lim)).flatMap g)
      (unitCost w + (env lim * (unitCost w + Tb + 4 * unitCost w + 1) + 2 * unitCost w + 1) +
        unitCost w * (x.length + 1)) ∧
    Inv (env lim) (runLoop (fun k e => exec x body
      (Function.update (Function.update e i k) xb (inBit x k))) (env lim) env).1 := by
  have HI := runLoop_inv (f := fun k e => exec x body
    (Function.update (Function.update e i k) xb (inBit x k))) (L := env lim)
    Inv h0 (fun k hk e he => (hs k hk e he).2)
  have H : ∀ k < env lim, Good x w body
      (Function.update (Function.update (runLoop (fun k e => exec x body
        (Function.update (Function.update e i k) xb (inBit x k))) k env).1 i k) xb (inBit x k))
      (g k) Tb := fun k hk => (hs k hk _ (HI k hk.le)).1
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
        ∑ k ∈ Finset.range (env lim), (unitCost w + Tb + 4 * unitCost w + 1) :=
      Finset.sum_le_sum fun k hk => by have := (H k (Finset.mem_range.mp hk)).cost_le; omega
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
    omega

lemma exec_loop_fst {N : ℕ} (i lim : Fin N) (body : Stm N) (env : Fin N → ℕ) :
    (exec x (loop i lim body) env).1 =
      Function.update (runLoop (fun k e => exec x body (Function.update e i k)) (env lim) env).1
        i (env lim) := rfl

lemma exec_loopX_fst {N : ℕ} (i lim xb : Fin N) (body : Stm N) (env : Fin N → ℕ) :
    (exec x (loopX i lim xb body) env).1 =
      Function.update (runLoop (fun k e => exec x body
        (Function.update (Function.update e i k) xb (inBit x k))) (env lim) env).1
        i (env lim) := rfl

end Stm

namespace Good

open Stm

variable {N : ℕ} {p q : Stm N} {env : Fin N → ℕ} {T₁ T₂ : ℕ}

lemma seq0 (h₁ : Good x w p env [] T₁) (h₂ : Good x w q (exec x p env).1 [] T₂) :
    Good x w (Stm.seq p q) env [] (T₁ + T₂) := (h₁.seq h₂).of_eq rfl le_rfl

end Good

/-! ## Expressions -/

/-- Expressions over a stack of naturals. -/
inductive Xp where
  | var (i : ℕ)
  | const (c : ℕ)
  | add (a b : Xp)
  | lt (a b : Xp)
  | half (a : Xp)
  | odd (a : Xp)
  | mulB (a b k : Xp)
  | shl (a k : Xp)
  | shr (a k : Xp)
  | xorM (a b k : Xp)

namespace Xp

/-- The value of an expression; level `i` of the stack `ρ` is `ρ.getD i 0`. -/
def eval (ρ : List ℕ) : Xp → ℕ
  | var i => ρ.getD i 0
  | const c => c
  | add a b => a.eval ρ + b.eval ρ
  | lt a b => if a.eval ρ < b.eval ρ then 1 else 0
  | half a => a.eval ρ / 2
  | odd a => a.eval ρ % 2
  | mulB a b k => a.eval ρ * (b.eval ρ % 2 ^ k.eval ρ)
  | shl a k => a.eval ρ * 2 ^ k.eval ρ
  | shr a k => a.eval ρ / 2 ^ k.eval ρ
  | xorM a b k => (a.eval ρ ^^^ b.eval ρ) % 2 ^ k.eval ρ

/-- The number of registers used from the target register on. -/
def need : Xp → ℕ
  | var _ => 1
  | const _ => 1
  | add a b => max a.need (b.need + 1)
  | lt a b => max a.need (b.need + 1)
  | half a => a.need
  | odd a => a.need
  | mulB a b k => max (max (a.need + 1) (b.need + 2)) (max (k.need + 3) 5)
  | shl a k => max (max a.need (k.need + 1)) 3
  | shr a k => max (max a.need (k.need + 1)) 3
  | xorM a b k => max (max (a.need + 1) (b.need + 2)) (max (k.need + 3) 6)

lemma one_le_need : ∀ e : Xp, 1 ≤ e.need
  | var _ => le_rfl
  | const _ => le_rfl
  | add a _ => le_trans (one_le_need a) (le_max_left _ _)
  | lt a _ => le_trans (one_le_need a) (le_max_left _ _)
  | half a => one_le_need a
  | odd a => one_le_need a
  | mulB .. => by simp only [need]; omega
  | shl .. => by simp only [need]; omega
  | shr .. => by simp only [need]; omega
  | xorM .. => by simp only [need]; omega

/-- Values stay below `B` (and the intermediate values of the loop-based operations). -/
def Fits (B : ℕ) (ρ : List ℕ) : Xp → Prop
  | var i => ρ.getD i 0 < B
  | const c => c < B
  | add a b => a.Fits B ρ ∧ b.Fits B ρ ∧ a.eval ρ + b.eval ρ < B
  | lt a b => a.Fits B ρ ∧ b.Fits B ρ
  | half a => a.Fits B ρ
  | odd a => a.Fits B ρ
  | mulB a b k => a.Fits B ρ ∧ b.Fits B ρ ∧ k.Fits B ρ ∧ a.eval ρ * 2 ^ k.eval ρ < B
  | shl a k => a.Fits B ρ ∧ k.Fits B ρ ∧ a.eval ρ * 2 ^ k.eval ρ < B
  | shr a k => a.Fits B ρ ∧ k.Fits B ρ
  | xorM a b k => a.Fits B ρ ∧ b.Fits B ρ ∧ k.Fits B ρ ∧ 2 ^ k.eval ρ < B

/-- The cost in units of `κ w`. -/
def cost (ρ : List ℕ) : Xp → ℕ
  | var _ => 1
  | const _ => 1
  | add a b => a.cost ρ + b.cost ρ + 1
  | lt a b => a.cost ρ + b.cost ρ + 1
  | half a => a.cost ρ + 1
  | odd a => a.cost ρ + 1
  | mulB a b k => a.cost ρ + b.cost ρ + k.cost ρ + k.eval ρ + 2
  | shl a k => a.cost ρ + k.cost ρ + k.eval ρ + 2
  | shr a k => a.cost ρ + k.cost ρ + k.eval ρ + 2
  | xorM a b k => a.cost ρ + b.cost ρ + k.cost ρ + k.eval ρ + 3

lemma eval_lt {B : ℕ} {ρ : List ℕ} : ∀ {e : Xp}, e.Fits B ρ → e.eval ρ < B
  | var _, h => h
  | const _, h => h
  | add _ _, h => h.2.2
  | lt a b, h => by
    have ha := eval_lt h.1; have hb := eval_lt h.2
    simp only [eval]; split_ifs <;> omega
  | half a, h => by have := eval_lt (e := a) h; simp only [eval]; omega
  | odd a, h => by
    have := eval_lt (e := a) h; simp only [eval]; have := Nat.mod_le (a.eval ρ) 2; omega
  | mulB a b k, h => by
    simp only [eval]
    have : b.eval ρ % 2 ^ k.eval ρ < 2 ^ k.eval ρ := Nat.mod_lt _ (by positivity)
    exact lt_of_le_of_lt (Nat.mul_le_mul_left _ this.le) h.2.2.2
  | shl _ _, h => h.2.2
  | shr a _, h => lt_of_le_of_lt (Nat.div_le_self _ _) (eval_lt h.1)
  | xorM _ _ _, h => lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) h.2.2.2.le

/-- The body of the multiplication loop. -/
def mulBody {N : ℕ} (res a b : Fin N) : Stm N :=
  .seq (.ite (.odd (.var b)) (.set res (.add (.var res) (.var a))) .skip)
    (.seq (.set b (.half (.var b))) (.set a (.add (.var a) (.var a))))

/-- Compilation into register `t`. -/
def comp (R d : ℕ) (A : List ℕ) : ℕ → Xp → Stm (R + 1)
  | t, var i => if i < d ∧ i ∉ A then .set (rg R t) (.var (rg R i)) else .set (rg R t) (.const 0)
  | t, const c => .set (rg R t) (.const c)
  | t, add a b => .seq (comp R d A t a) (.seq (comp R d A (t + 1) b)
      (.set (rg R t) (.add (.var (rg R t)) (.var (rg R (t + 1))))))
  | t, lt a b => .seq (comp R d A t a) (.seq (comp R d A (t + 1) b)
      (.set (rg R t) (.lt (.var (rg R t)) (.var (rg R (t + 1))))))
  | t, half a => .seq (comp R d A t a) (.set (rg R t) (.half (.var (rg R t))))
  | t, odd a => .seq (comp R d A t a) (.set (rg R t) (.odd (.var (rg R t))))
  | t, mulB a b k => .seq (comp R d A (t + 1) a) (.seq (comp R d A (t + 2) b)
      (.seq (comp R d A (t + 3) k) (.seq (.set (rg R t) (.const 0))
        (.loop (rg R (t + 4)) (rg R (t + 3)) (mulBody (rg R t) (rg R (t + 1)) (rg R (t + 2)))))))
  | t, shl a k => .seq (comp R d A t a) (.seq (comp R d A (t + 1) k)
      (Stm.shlS (rg R (t + 1)) (rg R t) (rg R (t + 2))))
  | t, shr a k => .seq (comp R d A t a) (.seq (comp R d A (t + 1) k)
      (Stm.shrS (rg R (t + 1)) (rg R t) (rg R (t + 2))))
  | t, xorM a b k => .seq (comp R d A (t + 1) a) (.seq (comp R d A (t + 2) b)
      (.seq (comp R d A (t + 3) k) (Stm.xorS (rg R (t + 1)) (rg R (t + 2)) (rg R t)
        (rg R (t + 4)) (rg R (t + 5)) (rg R (t + 3)))))

end Xp

end Lax119563Proofs.Reduction

namespace Lax119563Proofs.Reduction

variable {R : ℕ} {x : List Bool} {w : ℕ}

/-! ## Routines with fits and costs -/

section Routines

open Stm

variable {N : ℕ}

lemma exec_seq_fst (p q : Stm N) (env : Fin N → ℕ) :
    (exec x (Stm.seq p q) env).1 = (exec x q (exec x p env).1).1 := rfl

lemma exec_set_fst (r : Fin N) (e : Ex N) (env : Fin N → ℕ) :
    (exec x (Stm.set r e) env).1 = Function.update env r (e.eval env) := rfl

lemma nodeCost_ge (w : ℕ) : 64 ≤ unitCost w ∧ unitCost w ≤ Ex.nodeCost w :=
  ⟨by unfold unitCost; omega, Ex.unitCost_le_nodeCost w⟩

lemma shlS_good {k acc i : Fin N} (hia : i ≠ acc) (hka : k ≠ acc) (hik : i ≠ k)
    {env : Fin N → ℕ} {B : ℕ} (hB : 2 * B ≤ 2 ^ w) (hk : env k < B)
    (hv : env acc * 2 ^ env k < B) :
    Good x w (shlS k acc i) env [] (env k * (3 * Ex.nodeCost w + 5 * unitCost w + 1) +
      2 * unitCost w + 1) := by
  have H := good_loopInv (x := x) (w := w) (i := i) (lim := k)
    (body := Stm.set acc (Ex.add (Ex.var acc) (Ex.var acc))) (env := env)
    (fun j e => e acc = env acc * 2 ^ j ∧ e k = env k) (fun _ => [])
    (3 * Ex.nodeCost w + unitCost w) (by omega) ⟨by simp, rfl⟩ (by
      intro j hj e ⟨h1, h2⟩
      have e1 : Function.update e i j acc = env acc * 2 ^ j := by
        rw [Function.update_of_ne (Ne.symm hia), h1]
      have hle : env acc * 2 ^ (j + 1) ≤ env acc * 2 ^ env k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hj)
      have hle' : env acc * 2 ^ j ≤ env acc * 2 ^ (j + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      have e2 : env acc * 2 ^ (j + 1) = env acc * 2 ^ j + env acc * 2 ^ j := by ring
      refine ⟨(Good.set ?_).of_eq rfl (by simp [Ex.size]), ?_, ?_⟩
      · simp only [Ex.Fits, Ex.eval, e1]; omega
      · simp only [exec_set_fst, Function.update_self, Ex.eval, e1]; ring
      · rw [exec_set_fst, Function.update_of_ne hka, Function.update_of_ne (Ne.symm hik), h2])
  have := nodeCost_ge w
  exact H.1.of_eq (by simp) (le_of_eq (by ring))

lemma shrS_good {k acc i : Fin N} (hia : i ≠ acc) (hka : k ≠ acc) (hik : i ≠ k)
    {env : Fin N → ℕ} {B : ℕ} (hB : 2 * B ≤ 2 ^ w) (hk : env k < B) (hv : env acc < B) :
    Good x w (shrS k acc i) env [] (env k * (2 * Ex.nodeCost w + 5 * unitCost w + 1) +
      2 * unitCost w + 1) := by
  have H := good_loopInv (x := x) (w := w) (i := i) (lim := k)
    (body := Stm.set acc (Ex.half (Ex.var acc))) (env := env)
    (fun _ e => e acc ≤ env acc ∧ e k = env k) (fun _ => [])
    (2 * Ex.nodeCost w + unitCost w) (by omega) ⟨le_rfl, rfl⟩ (by
      intro j hj e ⟨h1, h2⟩
      have e1 : Function.update e i j acc = e acc := Function.update_of_ne (Ne.symm hia) _ _
      refine ⟨(Good.set ?_).of_eq rfl (by simp [Ex.size]), ?_, ?_⟩
      · simp only [Ex.Fits, e1]; omega
      · simp only [exec_set_fst, Function.update_self, Ex.eval, e1]; omega
      · rw [exec_set_fst, Function.update_of_ne hka, Function.update_of_ne (Ne.symm hik), h2])
  have := nodeCost_ge w
  exact H.1.of_eq (by simp) (le_of_eq (by ring))

lemma mulBody_step {res a b : Fin N} (hra : res ≠ a) (hrb : res ≠ b) (hab : a ≠ b)
    (e : Fin N → ℕ) {Av Bv j K B : ℕ} (hB : 2 * B ≤ 2 ^ w) (h1 : e res = Av * (Bv % 2 ^ j))
    (h2 : e a = Av * 2 ^ j) (h3 : e b = Bv / 2 ^ j) (hjK : j < K) (hAK : Av * 2 ^ K < B)
    (hBv : Bv < B) :
    Good x w (Xp.mulBody res a b) e [] (10 * Ex.nodeCost w + 3 * unitCost w + 1) ∧
      (exec x (Xp.mulBody res a b) e).1 res = Av * (Bv % 2 ^ (j + 1)) ∧
      (exec x (Xp.mulBody res a b) e).1 a = Av * 2 ^ (j + 1) ∧
      (exec x (Xp.mulBody res a b) e).1 b = Bv / 2 ^ (j + 1) ∧
      ∀ q, q ≠ res → q ≠ a → q ≠ b → (exec x (Xp.mulBody res a b) e).1 q = e q := by
  have hpow : Av * 2 ^ (j + 1) ≤ Av * 2 ^ K :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hjK)
  have hmod : Bv % 2 ^ j < 2 ^ j := Nat.mod_lt _ (by positivity)
  have hres : Av * (Bv % 2 ^ j) ≤ Av * 2 ^ j := Nat.mul_le_mul_left _ hmod.le
  have e2 : Av * 2 ^ (j + 1) = Av * 2 ^ j + Av * 2 ^ j := by ring
  have hmodS : Bv % 2 ^ (j + 1) = Bv % 2 ^ j + 2 ^ j * (Bv / 2 ^ j % 2) := Nat.mod_pow_succ
  have hbv : Bv / 2 ^ j ≤ Bv := Nat.div_le_self _ _
  have hdiv : Bv / 2 ^ j / 2 = Bv / 2 ^ (j + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]
  -- the conditional addition
  set e₁ : Fin N → ℕ := if Bv / 2 ^ j % 2 ≠ 0 then Function.update e res (e res + e a) else e
    with he₁
  have hite : Good x w (Stm.ite (.odd (.var b)) (.set res (.add (.var res) (.var a))) .skip) e []
      (2 * Ex.nodeCost w + 1 + (3 * Ex.nodeCost w + unitCost w)) ∧
      (exec x (Stm.ite (.odd (.var b)) (.set res (.add (.var res) (.var a))) .skip) e).1 = e₁ := by
    have hc : Ex.Fits w e (.odd (.var b) : Ex N) := by simp only [Ex.Fits]; omega
    by_cases hp : Bv / 2 ^ j % 2 ≠ 0
    · have hcv : (Ex.odd (.var b) : Ex N).eval e ≠ 0 := by simpa [Ex.eval, h3] using hp
      refine ⟨(Good.iteT hc hcv (Good.set ?_)).of_eq rfl (by simp [Ex.size]), ?_⟩
      · simp only [Ex.Fits, Ex.eval, h1, h2]; omega
      · rw [he₁, if_pos hp]; simp only [exec, Ex.eval] at hcv ⊢; simp [hcv]
    · have hcv : (Ex.odd (.var b) : Ex N).eval e = 0 := by
        simp only [Ex.eval, h3]; omega
      refine ⟨(Good.iteF hc hcv Good.skip).of_eq rfl (by simp [Ex.size]; try omega), ?_⟩
      simp only [exec, hcv, ne_eq, not_true_eq_false, if_false, he₁, if_neg hp]
  have r₁ : e₁ res = Av * (Bv % 2 ^ (j + 1)) := by
    rw [hmodS, he₁]
    split_ifs with hp
    · rw [Function.update_self, h1, h2]
      have : Bv / 2 ^ j % 2 = 1 := by omega
      rw [this]; ring
    · have : Bv / 2 ^ j % 2 = 0 := by omega
      rw [h1, this]; ring
  have o₁ : ∀ q, q ≠ res → e₁ q = e q := by
    intro q hq; rw [he₁]; split_ifs
    · exact Function.update_of_ne hq _ _
    · rfl
  have ea₁ : e₁ a = Av * 2 ^ j := by rw [o₁ a (Ne.symm hra), h2]
  have eb₁ : e₁ b = Bv / 2 ^ j := by rw [o₁ b (Ne.symm hrb), h3]
  have := nodeCost_ge w
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hs1 : Good x w (Stm.set b (.half (.var b))) e₁ []
        (2 * Ex.nodeCost w + unitCost w) :=
      (Good.set (by simp only [Ex.Fits, eb₁]; omega)).of_eq rfl (by simp [Ex.size])
    have hs2 : Good x w (Stm.set a (.add (.var a) (.var a)))
        (exec x (Stm.set b (.half (.var b))) e₁).1 [] (3 * Ex.nodeCost w + unitCost w) :=
      (Good.set (by
        simp only [Ex.Fits, Ex.eval, exec_set_fst, Function.update_of_ne hab, ea₁]
        omega)).of_eq rfl (by simp [Ex.size])
    have hs12 := Good.seq0 hs1 hs2
    rw [← hite.2] at hs12
    exact (Good.seq0 hite.1 hs12).mono (by omega)
  · simp only [Xp.mulBody, exec_seq_fst, hite.2, exec_set_fst, Function.update_of_ne hra,
      Function.update_of_ne hrb, r₁]
  · simp only [Xp.mulBody, exec_seq_fst, hite.2, exec_set_fst, Function.update_self, Ex.eval,
      Function.update_of_ne hab, ea₁, e2]
  · simp only [Xp.mulBody, exec_seq_fst, hite.2, exec_set_fst, Function.update_of_ne (Ne.symm hab),
      Function.update_self, Ex.eval, eb₁, hdiv]
  · intro q hq1 hq2 hq3
    simp only [Xp.mulBody, exec_seq_fst, hite.2, exec_set_fst, Function.update_of_ne hq2,
      Function.update_of_ne hq3, o₁ q hq1]

lemma xorBody_step {a b res pw : Fin N} (hab : a ≠ b) (har : a ≠ res) (hap : a ≠ pw)
    (hbr : b ≠ res) (hbp : b ≠ pw) (hrp : res ≠ pw) (e : Fin N → ℕ) {Av Bv j K B : ℕ}
    (hB : 2 * B ≤ 2 ^ w) (h1 : e res < 2 ^ j) (h2 : e pw = 2 ^ j) (h3 : e a ≤ Av)
    (h4 : e b ≤ Bv) (hjK : j < K) (hK : 2 ^ K < B) (hA : Av < B) (hBv : Bv < B) :
    Good x w (xorBody a b res pw) e [] (16 * Ex.nodeCost w + 4 * unitCost w + 1) ∧
      (exec x (xorBody a b res pw) e).1 res < 2 ^ (j + 1) ∧
      (exec x (xorBody a b res pw) e).1 pw = 2 ^ (j + 1) ∧
      (exec x (xorBody a b res pw) e).1 a ≤ Av ∧
      (exec x (xorBody a b res pw) e).1 b ≤ Bv ∧
      ∀ q, q ≠ a → q ≠ b → q ≠ res → q ≠ pw → (exec x (xorBody a b res pw) e).1 q = e q := by
  have hjp : 2 ^ (j + 1) ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hjK
  have e2 : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by ring
  set e₁ : Fin N → ℕ := if (Ex.odd (.add (.odd (.var a)) (.odd (.var b))) : Ex N).eval e ≠ 0 then Function.update e res (e res + e pw) else e
    with he₁
  have hite : Good x w (Stm.ite (Ex.odd (.add (.odd (.var a)) (.odd (.var b))) : Ex N) (.set res (.add (.var res) (.var pw))) .skip) e []
      (6 * Ex.nodeCost w + 1 + (3 * Ex.nodeCost w + unitCost w)) ∧
      (exec x (Stm.ite (Ex.odd (.add (.odd (.var a)) (.odd (.var b))) : Ex N) (.set res (.add (.var res) (.var pw))) .skip) e).1 = e₁ := by
    have hc : Ex.Fits w e (Ex.odd (.add (.odd (.var a)) (.odd (.var b))) : Ex N) := by
      simp only [Ex.Fits, Ex.eval]; omega
    by_cases hp : ((Ex.odd (.add (.odd (.var a)) (.odd (.var b))) : Ex N)).eval e ≠ 0
    · refine ⟨(Good.iteT hc hp (Good.set ?_)).of_eq rfl (by simp [Ex.size]), ?_⟩
      · simp only [Ex.Fits, Ex.eval]; omega
      · rw [he₁, if_pos hp]; simp only [exec]; rw [if_pos hp]; rfl
    · have hp' : ((Ex.odd (.add (.odd (.var a)) (.odd (.var b))) : Ex N)).eval e = 0 := by simpa using hp
      refine ⟨(Good.iteF hc hp' Good.skip).of_eq rfl (by simp [Ex.size]; try omega), ?_⟩
      rw [he₁, if_neg hp]; simp only [exec, if_neg hp]
  have o₁ : ∀ q, q ≠ res → e₁ q = e q := by
    intro q hq; rw [he₁]; split_ifs
    · exact Function.update_of_ne hq _ _
    · rfl
  have r₁ : e₁ res < 2 ^ (j + 1) := by
    rw [he₁]; split_ifs
    · rw [Function.update_self]; omega
    · omega
  have := nodeCost_ge w
  have hrest : ∀ f : Fin N → ℕ, f a ≤ Av → f b ≤ Bv → f pw = 2 ^ j →
      Good x w (Stm.seq (.set a (.half (.var a))) (.seq (.set b (.half (.var b)))
        (.set pw (.add (.var pw) (.var pw))))) f [] (7 * Ex.nodeCost w + 3 * unitCost w) := by
    intro f fa fb fp
    have g1 : Good x w (Stm.set a (.half (.var a))) f [] (2 * Ex.nodeCost w + unitCost w) :=
      (Good.set (by simp only [Ex.Fits]; omega)).of_eq rfl (by simp [Ex.size])
    have g2 : Good x w (Stm.set b (.half (.var b))) (exec x (Stm.set a (.half (.var a))) f).1 []
        (2 * Ex.nodeCost w + unitCost w) :=
      (Good.set (by simp only [Ex.Fits, exec_set_fst, Function.update_of_ne hab.symm]; omega)).of_eq
        rfl (by simp [Ex.size])
    have g3 : Good x w (Stm.set pw (.add (.var pw) (.var pw)))
        (exec x (Stm.set b (.half (.var b))) (exec x (Stm.set a (.half (.var a))) f).1).1 []
        (3 * Ex.nodeCost w + unitCost w) :=
      (Good.set (by
        simp only [Ex.Fits, Ex.eval, exec_set_fst, Function.update_of_ne hbp.symm,
          Function.update_of_ne hap.symm]
        omega)).of_eq rfl (by simp [Ex.size])
    exact (Good.seq0 g1 (Good.seq0 g2 g3)).mono (by omega)
  have hr := hrest e₁ (by rw [o₁ a har]; exact h3) (by rw [o₁ b hbr]; exact h4)
    (by rw [o₁ pw hrp.symm]; exact h2)
  rw [← hite.2] at hr
  refine ⟨(Good.seq0 hite.1 hr).mono (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [xorBody, exec_seq_fst, hite.2, exec_set_fst, Function.update_of_ne hrp,
      Function.update_of_ne hbr.symm, Function.update_of_ne har.symm]
    exact r₁
  · simp only [xorBody, exec_seq_fst, hite.2, exec_set_fst, Function.update_self,
      Function.update_of_ne hbp.symm, Function.update_of_ne hap.symm, Ex.eval, o₁ pw hrp.symm, h2]
    ring
  · simp only [xorBody, exec_seq_fst, hite.2, exec_set_fst, Function.update_of_ne hap,
      Function.update_of_ne hab, Function.update_self, Ex.eval, o₁ a har]
    have := Nat.div_le_self (e a) 2; omega
  · simp only [xorBody, exec_seq_fst, hite.2, exec_set_fst, Function.update_of_ne hbp,
      Function.update_self, Ex.eval, Function.update_of_ne hab.symm, o₁ b hbr]
    have := Nat.div_le_self (e b) 2; omega
  · intro q q1 q2 q3 q4
    simp only [xorBody, exec_seq_fst, hite.2, exec_set_fst, Function.update_of_ne q1,
      Function.update_of_ne q2, Function.update_of_ne q4, o₁ q q3]

lemma xorS_good {a b res pw t lim : Fin N} (hab : a ≠ b) (har : a ≠ res) (hap : a ≠ pw)
    (hat : a ≠ t) (hbr : b ≠ res) (hbp : b ≠ pw) (hbt : b ≠ t) (hrp : res ≠ pw)
    (hrt : res ≠ t) (hpt : pw ≠ t) (hla : lim ≠ a) (hlb : lim ≠ b) (hlr : lim ≠ res)
    (hlp : lim ≠ pw) (hlt : lim ≠ t) {env : Fin N → ℕ} {B : ℕ} (hB : 2 * B ≤ 2 ^ w)
    (hA : env a < B) (hBv : env b < B) (hK : 2 ^ env lim < B) :
    Good x w (xorS a b res pw t lim) env []
      (env lim * (16 * Ex.nodeCost w + 8 * unitCost w + 2) + 2 * Ex.nodeCost w +
        4 * unitCost w + 1) := by
  have := nodeCost_ge w
  have hKlt : env lim < 2 ^ env lim := Nat.lt_two_pow_self
  set env₀ := Function.update (Function.update env res 0) pw 1 with he₀
  have hL : env₀ lim = env lim := by
    rw [he₀, Function.update_of_ne hlp, Function.update_of_ne hlr]
  have g1 : Good x w (Stm.set res (.const 0)) env [] (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp only [Ex.Fits]; positivity)).of_eq rfl (by simp [Ex.size])
  have g2 : Good x w (Stm.set pw (.const 1)) (exec x (Stm.set res (.const 0)) env).1 []
      (Ex.nodeCost w + unitCost w) :=
    (Good.set (by have := Nat.one_le_two_pow (n := env lim); simp only [Ex.Fits]; omega)).of_eq rfl
      (by simp [Ex.size])
  have H := good_loopInv (x := x) (w := w) (i := t) (lim := lim) (body := xorBody a b res pw)
    (env := env₀) (fun j e => e res < 2 ^ j ∧ e pw = 2 ^ j ∧ e a ≤ env a ∧ e b ≤ env b)
    (fun _ => []) (16 * Ex.nodeCost w + 4 * unitCost w + 1) (by rw [hL]; omega)
    ⟨by simp [he₀, Function.update_of_ne hrp], by simp [he₀],
      by simp [he₀, Function.update_of_ne hap, Function.update_of_ne har],
      by simp [he₀, Function.update_of_ne hbp, Function.update_of_ne hbr]⟩ (by
      intro j hj e ⟨h1, h2, h3, h4⟩
      rw [hL] at hj
      have S := xorBody_step (x := x) hab har hap hbr hbp hrp (Function.update e t j) hB
        (by rw [Function.update_of_ne hrt]; exact h1) (by rw [Function.update_of_ne hpt]; exact h2)
        (by rw [Function.update_of_ne hat]; exact h3) (by rw [Function.update_of_ne hbt]; exact h4)
        hj hK hA hBv
      exact ⟨S.1, S.2.1, S.2.2.1, S.2.2.2.1, S.2.2.2.2.1⟩)
  rw [hL] at H
  have g3 : Good x w (Stm.loop t lim (xorBody a b res pw))
      (exec x (Stm.set pw (.const 1)) (exec x (Stm.set res (.const 0)) env).1).1 []
      (env lim * (16 * Ex.nodeCost w + 4 * unitCost w + 1 + 4 * unitCost w + 1) +
        2 * unitCost w + 1) := by
    have e0 : (exec x (Stm.set pw (.const 1)) (exec x (Stm.set res (.const 0)) env).1).1 = env₀ :=
      rfl
    rw [e0]; exact H.1.of_eq (by simp) le_rfl
  exact (Good.seq0 g1 (Good.seq0 g2 g3)).mono (by nlinarith)

end Routines

/-! ## Written registers -/

/-- All registers written by `c` satisfy `P`. -/
def WrIn {N : ℕ} (P : Fin N → Prop) (c : Stm N) : Prop := ∀ q, Stm.wr c q = true → P q

namespace WrIn

variable {N : ℕ} {P Q : Fin N → Prop} {p q : Stm N}

lemma mono (h : WrIn P p) (hPQ : ∀ r, P r → Q r) : WrIn Q p := fun r hr => hPQ r (h r hr)
lemma skip : WrIn P (Stm.skip : Stm N) := fun _ h => by simp [Stm.wr] at h
lemma emit {e : Ex N} : WrIn P (Stm.emit e) := fun _ h => by simp [Stm.wr] at h
lemma set {r : Fin N} {e : Ex N} (hr : P r) : WrIn P (Stm.set r e) := fun _ h => by
  simp only [Stm.wr, decide_eq_true_eq] at h; exact h ▸ hr
lemma len {r : Fin N} (hr : P r) : WrIn P (Stm.len r) := fun _ h => by
  simp only [Stm.wr, decide_eq_true_eq] at h; exact h ▸ hr
lemma seq (hp : WrIn P p) (hq : WrIn P q) : WrIn P (Stm.seq p q) := fun r h => by
  simp only [Stm.wr, Bool.or_eq_true] at h; exact h.elim (hp r) (hq r)
lemma ite {c : Ex N} (hp : WrIn P p) (hq : WrIn P q) : WrIn P (Stm.ite c p q) := fun r h => by
  simp only [Stm.wr, Bool.or_eq_true] at h; exact h.elim (hp r) (hq r)
lemma loop {i lim : Fin N} (hi : P i) (hp : WrIn P p) : WrIn P (Stm.loop i lim p) := fun r h => by
  simp only [Stm.wr, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact h ▸ hi
  · exact hp r h
lemma loopX {i lim xb : Fin N} (hi : P i) (hx : P xb) (hp : WrIn P p) :
    WrIn P (Stm.loopX i lim xb p) := fun r h => by
  simp only [Stm.wr, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · exact h ▸ hi
  · exact h ▸ hx
  · exact hp r h

lemma frame (h : WrIn P p) {r : Fin N} (hr : ¬ P r) (env : Fin N → ℕ) :
    (Stm.exec x p env).1 r = env r :=
  Stm.exec_frame p env r (by
    by_contra hc
    exact hr (h r (by simpa using hc)))

lemma wr_false (h : WrIn P p) {r : Fin N} (hr : ¬ P r) : Stm.wr p r = false := by
  by_contra hc
  exact hr (h r (by simpa using hc))

end WrIn

/-- Registers `≥ t`. -/
def Above (R t : ℕ) (q : Fin (R + 1)) : Prop := ∃ j, t ≤ j ∧ q = rg R j

lemma above_rg {R t j : ℕ} (h : t ≤ j) : Above R t (rg R j) := ⟨j, h, rfl⟩

lemma above_mono {R t t' : ℕ} (h : t ≤ t') {q : Fin (R + 1)} (hq : Above R t' q) : Above R t q := by
  obtain ⟨j, hj, rfl⟩ := hq; exact ⟨j, by omega, rfl⟩

lemma not_above {R t j : ℕ} (hj : j < t) (hjR : j < R) : ¬ Above R t (rg R j) := by
  rintro ⟨j', hj', he⟩
  exact rg_ne hjR (by omega) he

namespace Xp

variable {d : ℕ} {A : List ℕ}

lemma wrIn_comp (e : Xp) : ∀ t : ℕ, WrIn (Above R t) (comp R d A t e) := by
  induction e with
  | var i =>
    intro t; simp only [comp]; split_ifs
    · exact WrIn.set (above_rg le_rfl)
    · exact WrIn.set (above_rg le_rfl)
  | const c => intro t; exact WrIn.set (above_rg le_rfl)
  | add a b iha ihb =>
    intro t
    exact (iha t).seq (((ihb (t + 1)).mono fun _ => above_mono (by omega)).seq
      (WrIn.set (above_rg le_rfl)))
  | lt a b iha ihb =>
    intro t
    exact (iha t).seq (((ihb (t + 1)).mono fun _ => above_mono (by omega)).seq
      (WrIn.set (above_rg le_rfl)))
  | half a iha => intro t; exact (iha t).seq (WrIn.set (above_rg le_rfl))
  | odd a iha => intro t; exact (iha t).seq (WrIn.set (above_rg le_rfl))
  | mulB a b k iha ihb ihk =>
    intro t
    refine ((iha (t + 1)).mono fun _ => above_mono (by omega)).seq
      (((ihb (t + 2)).mono fun _ => above_mono (by omega)).seq
      (((ihk (t + 3)).mono fun _ => above_mono (by omega)).seq
      ((WrIn.set (above_rg le_rfl)).seq (WrIn.loop (above_rg (by omega)) ?_))))
    exact (WrIn.ite (WrIn.set (above_rg le_rfl)) WrIn.skip).seq
      ((WrIn.set (above_rg (by omega))).seq (WrIn.set (above_rg (by omega))))
  | shl a k iha ihk =>
    intro t
    exact (iha t).seq (((ihk (t + 1)).mono fun _ => above_mono (by omega)).seq
      (WrIn.loop (above_rg (by omega)) (WrIn.set (above_rg le_rfl))))
  | shr a k iha ihk =>
    intro t
    exact (iha t).seq (((ihk (t + 1)).mono fun _ => above_mono (by omega)).seq
      (WrIn.loop (above_rg (by omega)) (WrIn.set (above_rg le_rfl))))
  | xorM a b k iha ihb ihk =>
    intro t
    refine ((iha (t + 1)).mono fun _ => above_mono (by omega)).seq
      (((ihb (t + 2)).mono fun _ => above_mono (by omega)).seq
      (((ihk (t + 3)).mono fun _ => above_mono (by omega)).seq
      ((WrIn.set (above_rg le_rfl)).seq ((WrIn.set (above_rg (by omega))).seq
        (WrIn.loop (above_rg (by omega)) ?_)))))
    exact (WrIn.ite (WrIn.set (above_rg le_rfl)) WrIn.skip).seq
      ((WrIn.set (above_rg (by omega))).seq ((WrIn.set (above_rg (by omega))).seq
        (WrIn.set (above_rg (by omega)))))

lemma comp_frame (e : Xp) {t j : ℕ} (hj : j < t) (hjR : j < R) (env : Fin (R + 1) → ℕ) :
    (Stm.exec x (comp R d A t e) env).1 (rg R j) = env (rg R j) :=
  (wrIn_comp e t).frame (not_above hj hjR) env

end Xp

end Lax119563Proofs.Reduction
