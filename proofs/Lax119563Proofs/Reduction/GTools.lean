import Lax119563Proofs.Reduction.GMachine

/-!
# A toolkit for generators

* derived expressions: `Xp.eq`, `Xp.not`, `Xp.and`, `Xp.or` (on `0/1`), `Xp.mulC` (by a
  constant), `Xp.pow2`, with their values;
* derived generators: `Gn.seqL` (a static list), `Gn.when`, `Gn.dispatch v n f`
  (`f (value of v)` if it is `< n`), with their outputs;
* `Xp.Small W`: all values `< 2^W` and all loop counts `≤ W`; it implies
  `Xp.Fits (2^(2W))` and `cost ≤ size * (W + 3)`;
* uniform cost bounds for loops.
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

/-- The number of nodes. -/
def size : Xp → ℕ
  | var _ => 1
  | const _ => 1
  | add a b => a.size + b.size + 1
  | lt a b => a.size + b.size + 1
  | half a => a.size + 1
  | odd a => a.size + 1
  | mulB a b k => a.size + b.size + k.size + 1
  | shl a k => a.size + k.size + 1
  | shr a k => a.size + k.size + 1
  | xorM a b k => a.size + b.size + k.size + 1

/-- All values are below `2 ^ W` and all loop counts at most `W`. -/
def Small (W : ℕ) (ρ : List ℕ) : Xp → Prop
  | var i => ρ.getD i 0 < 2 ^ W
  | const c => c < 2 ^ W
  | add a b => a.Small W ρ ∧ b.Small W ρ ∧ a.eval ρ + b.eval ρ < 2 ^ W
  | lt a b => a.Small W ρ ∧ b.Small W ρ
  | half a => a.Small W ρ
  | odd a => a.Small W ρ
  | mulB a b k => a.Small W ρ ∧ b.Small W ρ ∧ k.Small W ρ ∧ k.eval ρ ≤ W ∧
      a.eval ρ * (b.eval ρ % 2 ^ k.eval ρ) < 2 ^ W
  | shl a k => a.Small W ρ ∧ k.Small W ρ ∧ k.eval ρ ≤ W ∧ a.eval ρ * 2 ^ k.eval ρ < 2 ^ W
  | shr a k => a.Small W ρ ∧ k.Small W ρ ∧ k.eval ρ ≤ W
  | xorM a b k => a.Small W ρ ∧ b.Small W ρ ∧ k.Small W ρ ∧ k.eval ρ ≤ W

end Xp

namespace Gn

variable {x : List Bool} {ρ : List ℕ}

/-- A static list of generators, in order. -/
def seqL : List Gn → Gn
  | [] => skip
  | g :: gs => seq g (seqL gs)

/-- `g` if `c ≠ 0`. -/
def when (c : Xp) (g : Gn) : Gn := ite c g skip

/-- `f i` for the value `i < n` of `v`; nothing if `v ≥ n`. -/
def dispatch (v : Xp) (n : ℕ) (f : ℕ → Gn) : Gn :=
  seqL ((List.range n).map fun i => when (Xp.eq v (.const i)) (f i))

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
