import Lax119563Proofs.Reduction.GTools

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
