import Lax119563Proofs.Reduction.EdgeJunc

/-!
# The previous step as a generator

`prevGen s D σX iX vX` (run at depth `D`) emits one entry per step `σ' < σ` such that some
step `σ'' ∈ [σ', σ)` has a nonzero check entry at the coordinate `(i, v)`; the steps are
enumerated as `q (s + ℓ) + j` by the step loops. `length_out_prevGen`: the length of its output
is `prevCnt`, so (`prevStep_eq_count`) it determines `trackAt`.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs Lax119563Proofs.Matrix

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

/-- The step `q (s + ℓ) + j` of the step loops entered at depth `D`. -/
def stepX (s D : ℕ) : Xp := add (mul (var (D + 1)) (add (const s) gℓ)) (var (D + 3))

namespace Gn

/-- The previous-step counter (entered at depth `D`). -/
def prevGen (s D : ℕ) (σX iX vX : Xp) : Gn :=
  stepLoops s (.count
    (stepLoops s (when (and (and (lt (stepX s (D + 5)) σX) (le (stepX s D) (stepX s (D + 5))))
      (entX s (var (D + 5 + 3)) iX vX)) (.emit (const 0))))
    (when (and (lt (stepX s D) σX) (not (eq (var (D + 4)) (const 0)))) (.emit (const 0))))

end Gn

lemma length_flatMap_ite {α : Type} (P : α → Prop) [DecidablePred P] (l : List α) :
    (l.flatMap fun a => if P a then [0] else []).length = (l.filter fun a => decide (P a)).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.filter_cons]
    by_cases h : P a <;> simp [h]; omega

lemma eval_stepX {τ : List ℕ} {D q j : ℕ} (hτ : τ.length = D) (hG : GlobOK M x s ℓ H τ)
    (l : List ℕ) : (stepX s D).eval (τ ++ [s + 2, q, s + ℓ, j] ++ l) = q * (s + ℓ) + j := by
  have hG' := (hG.append [s + 2, q, s + ℓ, j]).append l
  simp only [stepX, eval_add, eval_mul, eval_var, eval_const, hG'.eℓ]
  subst hτ
  rw [List.append_assoc, getD_app, getD_app]
  rfl

/-- Steps enumerated by the step loops, filtered. -/
lemma length_out_stepFlags {τ : List ℕ} (hG : GlobOK M x s ℓ H τ) (g : Gn)
    (P : ℕ → Prop) [DecidablePred P]
    (hg : ∀ q < s + 2, ∀ j < s + ℓ,
      g.out x (τ ++ [s + 2, q, s + ℓ, j]) = if P (q * (s + ℓ) + j) then [0] else []) :
    ((Gn.stepLoops s g).out x τ).length =
      ((List.range (numSteps (s + 1) ℓ)).filter fun σ => decide (P σ)).length := by
  rw [out_stepLoops hG, ← length_flatMap_ite, numSteps_succ, range_mul_flatMap]
  congr 1
  refine List.flatMap_congr fun q hq => List.flatMap_congr fun j hj => ?_
  rw [List.mem_range] at hq hj
  exact hg q hq j hj

lemma filter_range_lt {N σ : ℕ} (h : σ ≤ N) (P : ℕ → Bool) :
    (List.range N).filter (fun a => decide (a < σ) && P a) = (List.range σ).filter P := by
  have : List.range N = List.range σ ++ (List.range (N - σ)).map (σ + ·) := by
    rw [← List.range_add]; congr 1; omega
  rw [this, List.filter_append]
  have h2 : ((List.range (N - σ)).map (σ + ·)).filter (fun a => decide (a < σ) && P a) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
    simp
  rw [h2, List.append_nil]
  exact List.filter_congr fun a ha => by simp [List.mem_range.mp ha]

/-- **The previous-step counter.** -/
theorem length_out_prevGen {τ : List ℕ} {D σ : ℕ} (hτ : τ.length = D) (hG : GlobOK M x s ℓ H τ)
    {σX iX vX : Xp} (hσb : σX.Bnd D) (hib : iX.Bnd D) (hvb : vX.Bnd D) (hσ : σX.eval τ = σ)
    (hσN : σ ≤ numSteps (s + 1) ℓ) (hsℓ : 0 < s + ℓ) (c : Coord (s + 1) ℓ)
    (hi : iX.eval τ = c.1.val) (hv : vX.eval τ = regVal c.2) :
    ((Gn.prevGen s D σX iX vX).out x τ).length =
      prevCnt (fun σ' => decide (ent σ' c ≠ 0)) σ := by
  have ev : ∀ {e : Xp}, e.Bnd D → ∀ l, e.eval (τ ++ l) = e.eval τ := fun he l =>
    eval_append hτ l he
  unfold prevCnt
  rw [Gn.prevGen, length_out_stepFlags hG _ (fun σ' => σ' < σ ∧
    ((List.range σ).any fun σ'' => decide (σ' ≤ σ'') && decide (ent σ'' c ≠ 0)) = true)]
  · rw [← filter_range_lt hσN]
    congr 1
    refine List.filter_congr fun a _ => ?_
    by_cases h1 : a < σ
    · simp only [h1, decide_true, Bool.true_and]
      rw [Bool.eq_iff_iff]
      simp [List.any_eq_true]
    · simp [h1]
  intro q hq j hj
  set τ' := τ ++ [s + 2, q, s + ℓ, j]
  have hτ' : τ'.length = D + 4 := by simp [τ', hτ]
  have hGτ' : GlobOK M x s ℓ H τ' := hG.append _
  -- the inner count
  have hin : ((Gn.stepLoops s (Gn.when (and (and (lt (stepX s (D + 5)) σX)
      (le (stepX s D) (stepX s (D + 5)))) (entX s (var (D + 5 + 3)) iX vX))
      (.emit (const 0)))).out x (τ' ++ [0])).length =
      ((List.range (numSteps (s + 1) ℓ)).filter fun σ'' => decide (σ'' < σ ∧
        q * (s + ℓ) + j ≤ σ'' ∧ ent σ'' c ≠ 0)).length := by
    refine length_out_stepFlags (hGτ'.append [0]) _ _ fun q' hq' j' hj' => ?_
    rw [Gn.out_when]
    have hst : (stepX s (D + 5)).eval (τ' ++ [0] ++ [s + 2, q', s + ℓ, j']) =
        q' * (s + ℓ) + j' := by
      have := eval_stepX (τ := τ' ++ [0]) (D := D + 5) (q := q') (j := j') (by simp [hτ'])
        (hGτ'.append [0]) []
      rwa [List.append_nil] at this
    have hst' : (stepX s D).eval (τ' ++ [0] ++ [s + 2, q', s + ℓ, j']) = q * (s + ℓ) + j := by
      rw [show τ' ++ [0] ++ [s + 2, q', s + ℓ, j'] = τ ++ [s + 2, q, s + ℓ, j] ++
        ([0] ++ [s + 2, q', s + ℓ, j']) by simp [τ']]
      exact eval_stepX hτ hG _
    have hj'' : (var (D + 5 + 3)).eval (τ' ++ [0] ++ [s + 2, q', s + ℓ, j']) = j' := by
      rw [eval_var, show D + 5 + 3 = (τ' ++ [0]).length + 3 by simp [hτ'], getD_app]; rfl
    have hrest : ∀ {e : Xp}, e.Bnd D → e.eval (τ' ++ [0] ++ [s + 2, q', s + ℓ, j']) = e.eval τ :=
      fun he => by
        rw [show τ' ++ [0] ++ [s + 2, q', s + ℓ, j'] = τ ++ ([s + 2, q, s + ℓ, j] ++ [0] ++
          [s + 2, q', s + ℓ, j']) by simp [τ']]
        exact ev he _
    rw [eval_and' (eval_and' (eval_lt_eq _ _) (eval_le _ _)) (eval_entX _ _ _), hst, hst', hj'',
      hrest hσb, hrest hib, hrest hvb, hσ, hi, hv]
    have hent : ent (q' * (s + ℓ) + j') c ≠ 0 ↔ entB s j' c.1.val (regVal c.2) = true := by
      rw [ent_ne_zero_iff hsℓ, mod_step hj']
    simp only [hent, and_assoc]
    split_ifs <;> simp_all [Gn.out]
  rw [Gn.out, Gn.out_when]
  have hcnt : (var (D + 4)).eval (τ' ++ [((Gn.stepLoops s (Gn.when (and (and (lt (stepX s (D + 5)) σX)
      (le (stepX s D) (stepX s (D + 5)))) (entX s (var (D + 5 + 3)) iX vX))
      (.emit (const 0)))).out x (τ' ++ [0])).length]) =
      ((Gn.stepLoops s (Gn.when (and (and (lt (stepX s (D + 5)) σX)
      (le (stepX s D) (stepX s (D + 5)))) (entX s (var (D + 5 + 3)) iX vX))
      (.emit (const 0)))).out x (τ' ++ [0])).length := by
    rw [eval_var, List.getD_append_right _ _ _ _ (by rw [hτ'])]
    simp [hτ']
  have hst : (stepX s D).eval (τ' ++ [((Gn.stepLoops s (Gn.when (and (and (lt (stepX s (D + 5)) σX)
      (le (stepX s D) (stepX s (D + 5)))) (entX s (var (D + 5 + 3)) iX vX))
      (.emit (const 0)))).out x (τ' ++ [0])).length]) = q * (s + ℓ) + j := eval_stepX hτ hG _
  rw [eval_and' (eval_lt_eq _ _) (eval_not' (eval_eq' _ _)), hcnt, hst,
    eval_append hτ' _ (hσb.mono (by omega)), show σX.eval τ' = σ by rw [ev hσb, hσ], hin]
  simp only [eval_const]
  -- compare the conditions
  have key : ((List.range (numSteps (s + 1) ℓ)).filter fun σ'' => decide (σ'' < σ ∧
      q * (s + ℓ) + j ≤ σ'' ∧ ent σ'' c ≠ 0)).length ≠ 0 ↔
      ((List.range σ).any fun σ'' => decide (q * (s + ℓ) + j ≤ σ'') &&
        decide (ent σ'' c ≠ 0)) = true := by
    constructor
    · intro h
      obtain ⟨a, ha⟩ := List.exists_mem_of_length_pos (Nat.pos_of_ne_zero h)
      rw [List.mem_filter] at ha
      obtain ⟨-, ha⟩ := ha
      simp only [decide_eq_true_eq] at ha
      rw [List.any_eq_true]
      exact ⟨a, List.mem_range.mpr ha.1, by simp [ha.2.1, ha.2.2]⟩
    · intro h
      rw [List.any_eq_true] at h
      obtain ⟨a, ha, hb⟩ := h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      have ha' := List.mem_range.mp ha
      apply Nat.pos_iff_ne_zero.mp
      apply List.length_pos_of_mem (a := a)
      rw [List.mem_filter]
      exact ⟨List.mem_range.mpr (by omega), by simp [ha', hb.1, hb.2]⟩
  have key2 : (q * (s + ℓ) + j < σ ∧ ¬ ((List.range (numSteps (s + 1) ℓ)).filter fun σ'' =>
      decide (σ'' < σ ∧ q * (s + ℓ) + j ≤ σ'' ∧ ent σ'' c ≠ 0)).length = 0) ↔
      (q * (s + ℓ) + j < σ ∧ ((List.range σ).any fun σ'' => decide (q * (s + ℓ) + j ≤ σ'') &&
        decide (ent σ'' c ≠ 0)) = true) := and_congr_right' key
  simp only [key2]
  split_ifs <;> simp_all [Gn.out]

end Lax119563Proofs.Reduction
