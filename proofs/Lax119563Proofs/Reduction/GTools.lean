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
lemma cost_eq_const (a : Xp) (c : ℕ) : (eq a (const c)).cost ρ = 2 * a.cost ρ + 7 := by
  simp only [eq, cost]; ring

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

lemma Small.val_lt {W : ℕ} : ∀ {e : Xp}, e.Small W ρ → e.eval ρ < 2 ^ W
  | var _, h => h
  | const _, h => h
  | add _ _, h => h.2.2
  | lt a b, h => by
    have := Small.val_lt (e := a) h.1; have := Small.val_lt (e := b) h.2
    simp only [eval]; split_ifs <;> omega
  | half a, h => by have := Small.val_lt (e := a) h; simp only [eval]; omega
  | odd a, h => by
    have := Small.val_lt (e := a) h; simp only [eval]; have := Nat.mod_le (a.eval ρ) 2; omega
  | mulB _ _ _, h => h.2.2.2.2
  | shl _ _, h => h.2.2.2
  | shr a _, h => lt_of_le_of_lt (Nat.div_le_self _ _) (Small.val_lt h.1)
  | xorM _ _ k, h => lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
      (Nat.pow_le_pow_right (by norm_num) h.2.2.2)

lemma Small.fits {W : ℕ} (hW : 1 ≤ W) : ∀ {e : Xp}, e.Small W ρ → e.Fits (2 ^ (2 * W)) ρ
  | var _, h => lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega))
  | const _, h => lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega))
  | add a b, h => ⟨Small.fits hW h.1, Small.fits hW h.2.1,
      lt_of_lt_of_le h.2.2 (Nat.pow_le_pow_right (by norm_num) (by omega))⟩
  | lt a b, h => ⟨Small.fits hW h.1, Small.fits hW h.2⟩
  | half a, h => Small.fits (e := a) hW h
  | odd a, h => Small.fits (e := a) hW h
  | mulB a b k, h => by
    refine ⟨Small.fits hW h.1, Small.fits hW h.2.1, Small.fits hW h.2.2.1, ?_⟩
    have ha := Small.val_lt h.1
    have hk : 2 ^ k.eval ρ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) h.2.2.2.1
    calc a.eval ρ * 2 ^ k.eval ρ < 2 ^ W * 2 ^ W :=
          Nat.mul_lt_mul_of_lt_of_le ha hk (by positivity)
      _ = 2 ^ (2 * W) := by rw [← pow_add]; ring_nf
  | shl a k, h => ⟨Small.fits hW h.1, Small.fits hW h.2.1,
      lt_of_lt_of_le h.2.2.2 (Nat.pow_le_pow_right (by norm_num) (by omega))⟩
  | shr a k, h => ⟨Small.fits hW h.1, Small.fits hW h.2.1⟩
  | xorM a b k, h => ⟨Small.fits hW h.1, Small.fits hW h.2.1, Small.fits hW h.2.2.1,
      lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) h.2.2.2)
        (Nat.pow_lt_pow_right (by norm_num) (by omega))⟩

lemma Small.cost_le {W : ℕ} : ∀ {e : Xp}, e.Small W ρ → e.cost ρ ≤ e.size * (W + 3)
  | var _, _ => by simp [cost, size]
  | const _, _ => by simp [cost, size]
  | add a b, h => by
    have := Small.cost_le h.1; have := Small.cost_le h.2.1
    simp only [cost, size]; nlinarith
  | lt a b, h => by
    have := Small.cost_le h.1; have := Small.cost_le h.2
    simp only [cost, size]; nlinarith
  | half a, h => by have := Small.cost_le (e := a) h; simp only [cost, size]; nlinarith
  | odd a, h => by have := Small.cost_le (e := a) h; simp only [cost, size]; nlinarith
  | mulB a b k, h => by
    have := Small.cost_le h.1; have := Small.cost_le h.2.1; have := Small.cost_le h.2.2.1
    have := h.2.2.2.1
    simp only [cost, size]; nlinarith
  | shl a k, h => by
    have := Small.cost_le h.1; have := Small.cost_le h.2.1; have := h.2.2.1
    simp only [cost, size]; nlinarith
  | shr a k, h => by
    have := Small.cost_le h.1; have := Small.cost_le h.2.1; have := h.2.2
    simp only [cost, size]; nlinarith
  | xorM a b k, h => by
    have := Small.cost_le h.1; have := Small.cost_le h.2.1; have := Small.cost_le h.2.2.1
    have := h.2.2.2
    simp only [cost, size]; nlinarith

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

lemma out_dispatch (v : Xp) (n : ℕ) (f : ℕ → Gn) :
    (dispatch v n f).out x ρ = if v.eval ρ < n then (f (v.eval ρ)).out x ρ else [] := by
  rw [dispatch, out_seqL, List.flatMap_map, ← flatMap_range_ite n (v.eval ρ)
    (fun i => (f i).out x ρ)]
  refine List.flatMap_congr fun i _ => ?_
  simp only [out_when, Xp.eval_eq, Xp.eval]
  split_ifs <;> simp_all

/-! ### Fits and costs of derived generators -/

variable {B : ℕ}

lemma fits_seqL (gs : List Gn) (h : ∀ g ∈ gs, g.Fits x B ρ) : (seqL gs).Fits x B ρ := by
  induction gs with
  | nil => trivial
  | cons g gs ih =>
    exact ⟨h g (by simp), ih fun g' hg' => h g' (by simp [hg'])⟩

lemma cost_seqL (gs : List Gn) :
    (seqL gs).cost x ρ = (gs.map fun g => g.cost x ρ).sum + 1 := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [seqL, cost, ih, List.map_cons, List.sum_cons]; ring

lemma fits_when {c : Xp} {g : Gn} (hc : c.Fits B ρ) (hg : c.eval ρ ≠ 0 → g.Fits x B ρ) :
    (when c g).Fits x B ρ := by
  refine ⟨hc, ?_⟩
  split_ifs with h
  · exact hg h
  · trivial

lemma cost_when_le {c : Xp} {g : Gn} {T : ℕ} (hg : c.eval ρ ≠ 0 → g.cost x ρ ≤ T) :
    (when c g).cost x ρ ≤ c.cost ρ + 2 + T := by
  simp only [when, cost]
  split_ifs with h
  · have := hg h; omega
  · omega

lemma fits_dispatch {v : Xp} {n : ℕ} {f : ℕ → Gn} (hv : v.Fits B ρ) (hn : n < B)
    (hf : v.eval ρ < n → (f (v.eval ρ)).Fits x B ρ) : (dispatch v n f).Fits x B ρ := by
  have hvB := Xp.eval_lt hv
  refine fits_seqL _ fun g hg => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
  rw [List.mem_range] at hi
  refine fits_when ⟨⟨⟨hv, (by show i < B; omega)⟩, ⟨(by show i < B; omega), hv⟩, ?_⟩,
    (by show 1 < B; omega)⟩ fun h => ?_
  · show (if v.eval ρ < i then 1 else 0) + (if i < v.eval ρ then 1 else 0) < B
    split_ifs <;> omega
  · have : v.eval ρ = i := by
      by_contra hne; simp [Xp.eval_eq, Xp.eval, hne] at h
    subst this; exact hf hi

lemma sum_range_ite (n v T : ℕ) :
    ((List.range n).map fun i => if v = i then T else 0).sum = if v < n then T else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    by_cases h1 : v < n
    · simp [h1, show v < n + 1 by omega, show v ≠ n by omega]
    · by_cases h2 : v = n
      · subst h2; simp
      · simp [h1, h2, show ¬ v < n + 1 by omega]

lemma cost_dispatch_le {v : Xp} {n : ℕ} {f : ℕ → Gn} {T : ℕ}
    (hf : v.eval ρ < n → (f (v.eval ρ)).cost x ρ ≤ T) :
    (dispatch v n f).cost x ρ ≤ n * (2 * v.cost ρ + 9) + T + 1 := by
  rw [dispatch, cost_seqL, List.map_map]
  have key : ∀ i ∈ List.range n, ((fun g : Gn => g.cost x ρ) ∘
      (fun i => when (Xp.eq v (.const i)) (f i))) i ≤
      (2 * v.cost ρ + 9) + (if v.eval ρ = i then T else 0) := by
    intro i hi
    simp only [Function.comp, when, cost, Xp.cost_eq_const, Xp.eval_eq_const]
    by_cases h : v.eval ρ = i
    · subst h; have := hf (List.mem_range.mp hi); simp; omega
    · simp [h]
  have hsum := List.sum_le_sum key
  rw [List.sum_map_add, List.map_const', List.sum_replicate, List.length_range,
    smul_eq_mul, sum_range_ite] at hsum
  have : (if v.eval ρ < n then T else 0) ≤ T := by split_ifs <;> omega
  omega

lemma cost_loop_le {lim : Xp} {g : Gn} {T : ℕ}
    (hb : ∀ k < lim.eval ρ, g.cost x (ρ ++ [lim.eval ρ, k]) ≤ T) :
    (loop lim g).cost x ρ ≤ lim.cost ρ + 1 + lim.eval ρ * (T + 1) := by
  simp only [cost]
  have : ∑ k ∈ Finset.range (lim.eval ρ), (g.cost x (ρ ++ [lim.eval ρ, k]) + 1) ≤
      ∑ k ∈ Finset.range (lim.eval ρ), (T + 1) :=
    Finset.sum_le_sum fun k hk => by have := hb k (Finset.mem_range.mp hk); omega
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
  omega

lemma cost_loopX_le {lim : Xp} {g : Gn} {T : ℕ}
    (hb : ∀ k < lim.eval ρ, g.cost x (ρ ++ [lim.eval ρ, k, inBit x k]) ≤ T) :
    (loopX lim g).cost x ρ ≤ lim.cost ρ + 2 + x.length + lim.eval ρ * (T + 1) := by
  simp only [cost]
  have : ∑ k ∈ Finset.range (lim.eval ρ), (g.cost x (ρ ++ [lim.eval ρ, k, inBit x k]) + 1) ≤
      ∑ k ∈ Finset.range (lim.eval ρ), (T + 1) :=
    Finset.sum_le_sum fun k hk => by have := hb k (Finset.mem_range.mp hk); omega
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
  omega

end Gn

end Lax119563Proofs.Reduction
