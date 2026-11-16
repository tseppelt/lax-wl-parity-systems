import Lax119563Proofs.Reduction.GuardEval
import Lax119563Proofs.Reduction.SchFinal

/-!
# The domain test as a generator

`violGen s d iX vX xbX gkX g1X g2X g3X ℓX HX` (run at depth `d`) emits nothing iff the
coordinate with block `i` and register value `v` lies in the domain described by the guard
numbers `[gk, g1, g2, g3]`, i.e. `i = s ∨ gEval x ℓ H [gk, g1, g2, g3] i v`
(`violGen_out_eq_nil_iff`; `xbX` must evaluate to `inBit x v`). Used under `Gn.count`, it
pushes `0` iff the coordinate is in the domain.
-/

namespace Lax119563Proofs.Reduction

open Circuits Xp

namespace Xp

variable {ρ : List ℕ}

/-- `a ≤ b`. -/
def le (a b : Xp) : Xp := not (lt b a)

lemma eval_bool {e : Xp} {P : Prop} [Decidable P] (h : e.eval ρ = if P then 1 else 0) :
    e.eval ρ ≤ 1 := by
  rw [h]; split_ifs <;> omega

lemma eval_and' {a b : Xp} {P Q : Prop} [Decidable P] [Decidable Q]
    (ha : a.eval ρ = if P then 1 else 0) (hb : b.eval ρ = if Q then 1 else 0) :
    (and a b).eval ρ = if P ∧ Q then 1 else 0 := by
  rw [eval_and (eval_bool ha) (eval_bool hb), ha, hb]
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

lemma eval_or' {a b : Xp} {P Q : Prop} [Decidable P] [Decidable Q]
    (ha : a.eval ρ = if P then 1 else 0) (hb : b.eval ρ = if Q then 1 else 0) :
    (or a b).eval ρ = if P ∨ Q then 1 else 0 := by
  rw [eval_or, ha, hb]
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

lemma eval_not' {a : Xp} {P : Prop} [Decidable P] (ha : a.eval ρ = if P then 1 else 0) :
    (not a).eval ρ = if ¬ P then 1 else 0 := by
  rw [eval_not, ha]
  by_cases hP : P <;> simp [hP]

lemma eval_le (a b : Xp) : (le a b).eval ρ = if a.eval ρ ≤ b.eval ρ then 1 else 0 := by
  rw [le, eval_not' (P := b.eval ρ < a.eval ρ) (by rw [eval_lt_eq])]
  by_cases h : a.eval ρ ≤ b.eval ρ
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

lemma eval_eq' (a b : Xp) : (eq a b).eval ρ = if a.eval ρ = b.eval ρ then 1 else 0 :=
  eval_eq a b

@[simp] lemma eval_odd (a : Xp) : (odd a).eval ρ = a.eval ρ % 2 := rfl
@[simp] lemma eval_shr (a k : Xp) : (shr a k).eval ρ = a.eval ρ / 2 ^ k.eval ρ := rfl
@[simp] lemma eval_xorM (a b k : Xp) :
    (xorM a b k).eval ρ = (a.eval ρ ^^^ b.eval ρ) % 2 ^ k.eval ρ := rfl

end Xp

/-! ## Arithmetic of the field guard -/

lemma div_eq_iff_window {a ℓ i : ℕ} (hℓ : 0 < ℓ) : a / ℓ = i ↔ i * ℓ ≤ a ∧ a < i * ℓ + ℓ := by
  constructor
  · rintro rfl
    exact ⟨Nat.div_mul_le_self a ℓ, by have := Nat.lt_div_mul_add (a := a) hℓ; linarith⟩
  · rintro ⟨h1, h2⟩
    exact Nat.div_eq_of_lt_le h1 (by rw [Nat.succ_mul]; exact h2)

lemma testBit_eq_mod (v j : ℕ) : v.testBit j = decide (v / 2 ^ j % 2 = 1) :=
  Nat.testBit_eq_decide_div_mod_eq

lemma shift_bit (v a j : ℕ) : v * 2 ^ a / 2 ^ (a + j) = v / 2 ^ j := by
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (by positivity)]

/-- A violation of the field guard at offset `t`. -/
lemma fieldBad_iff {ℓ k t i v q : ℕ} (hℓ : 0 < ℓ) :
    ((k + t) / ℓ = i ∧ v.testBit ((k + t) % ℓ) ≠ q.testBit t) ↔
      (i * ℓ ≤ k + t ∧ k + t < i * ℓ + ℓ ∧ v * 2 ^ (i * ℓ) / 2 ^ (k + t) % 2 ≠ q / 2 ^ t % 2) := by
  rw [div_eq_iff_window hℓ]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, ?_⟩
    obtain ⟨j, hj⟩ : ∃ j, k + t = i * ℓ + j := ⟨k + t - i * ℓ, by omega⟩
    have hm : (k + t) % ℓ = j := by
      rw [hj, Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
    rw [hm, testBit_eq_mod, testBit_eq_mod] at h3
    rw [hj, shift_bit]
    intro h; apply h3; rw [h]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    obtain ⟨j, hj⟩ : ∃ j, k + t = i * ℓ + j := ⟨k + t - i * ℓ, by omega⟩
    have hm : (k + t) % ℓ = j := by
      rw [hj, Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
    rw [hm, testBit_eq_mod, testBit_eq_mod]
    rw [hj, shift_bit] at h3
    intro h
    apply h3
    have e1 := Nat.mod_two_eq_zero_or_one (v / 2 ^ j)
    have e2 := Nat.mod_two_eq_zero_or_one (q / 2 ^ t)
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;> simp_all

lemma fieldOK_iff {ℓ k m q i v : ℕ} (hℓ : 0 < ℓ) :
    fieldOK ℓ k m q i v = true ↔ ∀ t < m, ¬ (i * ℓ ≤ k + t ∧ k + t < i * ℓ + ℓ ∧
      v * 2 ^ (i * ℓ) / 2 ^ (k + t) % 2 ≠ q / 2 ^ t % 2) := by
  simp only [fieldOK, decide_eq_true_eq]
  refine forall_congr' fun t => imp_congr_right fun _ => ?_
  rw [← fieldBad_iff hℓ]
  tauto

/-! ## The generator -/

/-- The field `field (2^H) (iℓ) ℓ`. -/
def fieldX (iℓX ℓX HX : Xp) : Xp := xorM (shr (pow2 HX) iℓX) (const 0) ℓX

/-- The number `initCV x ν v` from `xb = inBit x v`. -/
def initCVX (νX vX xbX : Xp) : Xp :=
  add (eq vX (const 0)) (mulC 2 (mul xbX (eq νX (const 0))))

/-- A violation of the field guard at offset `t`. -/
def fieldBadX (iℓX kX tX vX qX ℓX : Xp) : Xp :=
  and (and (le iℓX (add kX tX)) (lt (add kX tX) (add iℓX ℓX)))
    (not (eq (odd (shr (shl vX iℓX) (add kX tX))) (odd (shr qX tX))))

/-- **The domain violations** (at depth `d`). -/
def violGen (s d : ℕ) (iX vX xbX gkX g1X g2X g3X ℓX HX : Xp) : Gn :=
  Gn.when (not (eq iX (const s)))
    (.ite (eq gkX (const 0))
      (.loop g2X (Gn.when (fieldBadX (mul ℓX iX) g1X (var (d + 1)) vX g3X ℓX) (.emit (const 0))))
      (.ite (eq gkX (const 1))
        (Gn.when (not (or (and (eq iX (const 0)) (eq (initCVX g1X vX xbX) g2X))
            (and (not (eq iX (const 0))) (eq vX (fieldX (mul ℓX iX) ℓX HX)))))
          (.emit (const 0)))
        (.ite (eq gkX (const 2))
          (Gn.when (not (or (not (eq iX g1X)) (not (eq vX (fieldX (mul ℓX iX) ℓX HX)))))
            (.emit (const 0)))
          (Gn.when (not (eq vX (const 0))) (.emit (const 0))))))

lemma eval_fieldX {ρ : List ℕ} (iℓX ℓX HX : Xp) :
    (fieldX iℓX ℓX HX).eval ρ = field (2 ^ HX.eval ρ) (iℓX.eval ρ) (ℓX.eval ρ) := by
  simp [fieldX, field]

lemma eval_initCVX {ρ : List ℕ} {x : List Bool} {ν v : ℕ} {νX vX xbX : Xp}
    (hν : νX.eval ρ = ν) (hv : vX.eval ρ = v) (hxb : xbX.eval ρ = inBit x v) :
    (initCVX νX vX xbX).eval ρ = initCV x ν v := by
  simp only [initCVX, initCV, Xp.eval_add, Xp.eval_eq, Xp.eval_const, Xp.eval_mulC, Xp.eval_mul,
    hν, hv, hxb]
  by_cases h : ν = 0 <;> simp [h]

theorem violGen_out_eq_nil_iff {x : List Bool} {τ : List ℕ} {s d : ℕ}
    {iX vX xbX gkX g1X g2X g3X ℓX HX : Xp} (hτ : τ.length = d)
    (hb : ∀ e ∈ [iX, vX, xbX, gkX, g1X, g2X, g3X, ℓX, HX], e.Bnd d)
    {i v gk g1 g2 g3 ℓ H : ℕ} (hi : iX.eval τ = i) (hv : vX.eval τ = v)
    (hxb : xbX.eval τ = inBit x v) (hgk : gkX.eval τ = gk) (hg1 : g1X.eval τ = g1)
    (hg2 : g2X.eval τ = g2) (hg3 : g3X.eval τ = g3) (hℓX : ℓX.eval τ = ℓ) (hHX : HX.eval τ = H)
    (hℓ : 0 < ℓ) :
    (violGen s d iX vX xbX gkX g1X g2X g3X ℓX HX).out x τ = [] ↔
      (i = s ∨ gEval x ℓ H [gk, g1, g2, g3] i v = true) := by
  have hiℓ : (mul ℓX iX).eval τ = i * ℓ := by rw [Xp.eval_mul, hℓX, hi, Nat.mul_comm]
  have hfx : (fieldX (mul ℓX iX) ℓX HX).eval τ = field (2 ^ H) (i * ℓ) ℓ := by
    rw [eval_fieldX, hiℓ, hℓX, hHX]
  have hB : ∀ e ∈ [iX, vX, xbX, gkX, g1X, g2X, g3X, ℓX, HX], e.Bnd d := hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hB
  obtain ⟨bi, bv, -, -, bg1, -, bg3, bℓ, -⟩ := hB
  have hns : (not (eq iX (const s))).eval τ = if ¬ i = s then 1 else 0 :=
    Xp.eval_not' (by rw [Xp.eval_eq, hi, Xp.eval_const])
  have e0 : (eq gkX (const 0)).eval τ = if gk = 0 then 1 else 0 := by
    rw [Xp.eval_eq, hgk, Xp.eval_const]
  have e1 : (eq gkX (const 1)).eval τ = if gk = 1 then 1 else 0 := by
    rw [Xp.eval_eq, hgk, Xp.eval_const]
  have e2 : (eq gkX (const 2)).eval τ = if gk = 2 then 1 else 0 := by
    rw [Xp.eval_eq, hgk, Xp.eval_const]
  have hbad : ∀ t, (fieldBadX (mul ℓX iX) g1X (var (d + 1)) vX g3X ℓX).eval (τ ++ [g2, t]) =
      if (i * ℓ ≤ g1 + t ∧ g1 + t < i * ℓ + ℓ) ∧
        ¬ v * 2 ^ (i * ℓ) / 2 ^ (g1 + t) % 2 = g3 / 2 ^ t % 2 then 1 else 0 := by
    intro t
    have hev : ∀ e : Xp, e.Bnd d → e.eval (τ ++ [g2, t]) = e.eval τ :=
      fun e he => Xp.eval_append hτ _ he
    have ht' : (var (d + 1)).eval (τ ++ [g2, t]) = t := by
      simp only [Xp.eval_var]
      rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hτ]
    have hm : (mul ℓX iX).eval (τ ++ [g2, t]) = i * ℓ := by
      rw [Xp.eval_mul, hev _ bℓ, hev _ bi, hℓX, hi, Nat.mul_comm]
    have hk : (add g1X (var (d + 1))).eval (τ ++ [g2, t]) = g1 + t := by
      rw [Xp.eval_add, hev _ bg1, ht', hg1]
    refine Xp.eval_and' (Xp.eval_and' ?_ ?_) (Xp.eval_not' ?_)
    · rw [Xp.eval_le, hm, hk]
    · rw [Xp.eval_lt_eq, hk, Xp.eval_add, hm, hev _ bℓ, hℓX]
    · rw [Xp.eval_eq]
      simp only [Xp.eval_odd, Xp.eval_shr, Xp.eval_shl, hm, hk, ht', hev _ bv, hev _ bg3, hv, hg3]
  have hhit : (not (or (and (eq iX (const 0)) (eq (initCVX g1X vX xbX) g2X))
      (and (not (eq iX (const 0))) (eq vX (fieldX (mul ℓX iX) ℓX HX))))).eval τ =
      if ¬ ((i = 0 ∧ initCV x g1 v = g2) ∨ (¬ i = 0 ∧ v = field (2 ^ H) (i * ℓ) ℓ)) then 1
        else 0 :=
    Xp.eval_not' (Xp.eval_or' (Xp.eval_and' (by rw [Xp.eval_eq, hi, Xp.eval_const])
        (by rw [Xp.eval_eq, eval_initCVX hg1 hv hxb, hg2]))
      (Xp.eval_and' (Xp.eval_not' (by rw [Xp.eval_eq, hi, Xp.eval_const]))
        (by rw [Xp.eval_eq, hv, hfx])))
  have hmiss : (not (or (not (eq iX g1X)) (not (eq vX (fieldX (mul ℓX iX) ℓX HX))))).eval τ =
      if ¬ (¬ i = g1 ∨ ¬ v = field (2 ^ H) (i * ℓ) ℓ) then 1 else 0 :=
    Xp.eval_not' (Xp.eval_or' (Xp.eval_not' (by rw [Xp.eval_eq, hi, hg1]))
      (Xp.eval_not' (by rw [Xp.eval_eq, hv, hfx])))
  have hz : (not (eq vX (const 0))).eval τ = if ¬ v = 0 then 1 else 0 :=
    Xp.eval_not' (by rw [Xp.eval_eq, hv, Xp.eval_const])
  simp only [violGen, Gn.out_when, Gn.out, hns, e0, e1, e2, hhit, hmiss, hz, hg2, hbad]
  by_cases his : i = s
  · simp [his]
  · rcases (show gk = 0 ∨ gk = 1 ∨ gk = 2 ∨ 3 ≤ gk by omega) with h0 | h1 | h2 | h3
    · subst h0
      simp only [his, gEval, List.getD_cons_zero, List.getD_cons_succ, fieldOK_iff hℓ]
      simp only [not_false_eq_true, if_true, ne_eq, one_ne_zero, false_or,
        List.flatMap_eq_nil_iff, List.mem_range, ite_eq_right_iff, reduceCtorEq, imp_false,
        Decidable.not_not, if_false]
      refine forall_congr' fun t => imp_congr_right fun _ => ?_
      rw [and_assoc]
    · subst h1
      have c0 : (if ¬i = s then 1 else 0) ≠ 0 := by simp [his]
      rw [if_pos c0, if_neg (by simp), if_pos (by simp)]
      have : gEval x ℓ H [1, g1, g2, g3] i v = (if i = 0 then decide (initCV x g1 v = g2)
          else decide (v = field (2 ^ H) (i * ℓ) ℓ)) := rfl
      rw [this]
      generalize field (2 ^ H) (i * ℓ) ℓ = F
      generalize initCV x g1 v = C
      by_cases hi0 : i = 0 <;> by_cases hc : C = g2 <;> by_cases hF : v = F <;>
        simp [his, hi0, hc, hF] <;> omega
    · subst h2
      have c0 : (if ¬i = s then 1 else 0) ≠ 0 := by simp [his]
      rw [if_pos c0, if_neg (by simp), if_neg (by simp), if_pos (by simp)]
      have : gEval x ℓ H [2, g1, g2, g3] i v = (if i = g1 then decide (v ≠ field (2 ^ H) (i * ℓ) ℓ)
          else true) := rfl
      rw [this]
      generalize field (2 ^ H) (i * ℓ) ℓ = F
      by_cases hig : i = g1 <;> by_cases hF : v = F <;> simp [his, hig, hF] <;> omega
    · have : gEval x ℓ H [gk, g1, g2, g3] i v = decide (v = 0) := by
        unfold gEval
        simp only [List.getD_cons_zero]
        rcases gk with _ | _ | _ | gk
        · omega
        · omega
        · omega
        · rfl
      rw [this]
      have g0 : gk ≠ 0 := by omega
      have g1' : gk ≠ 1 := by omega
      have g2' : gk ≠ 2 := by omega
      by_cases hv0 : v = 0 <;> simp [his, hv0, g0, g1', g2']


/-- **The domain test on a schema stack.** On a stack `σ` extending a schema stack `τ`
(record from level `b + 28`, guard numbers at `b + 33 … b + 36`), the violations are empty
iff the coordinate is in the domain of the schema. -/
theorem violGen_nil_iff_mem {M : Lax489179.TuringMachine.Machine} {x : List Bool} {s ℓ H N b d : ℕ}
    {sc : Lax119563.ImplicitParitySystems.Schema (s + 1) ℓ N} {τ σ : List ℕ}
    (hτ : τ.length = b + 37) (hrec : SchRec M x s ℓ H sc (τ.drop (b + 28)))
    (hσ : σ.length = d) (hστ : σ.take (b + 37) = τ) (hd : b + 37 ≤ d)
    {iX vX xbX ℓX HX : Xp} (hb : ∀ e ∈ [iX, vX, xbX, ℓX, HX], e.Bnd d)
    (c : Lax119563.ImplicitParitySystems.Coord (s + 1) ℓ)
    (hi : iX.eval σ = c.1.val) (hv : vX.eval σ = regVal c.2)
    (hxb : xbX.eval σ = inBit x (regVal c.2)) (hℓX : ℓX.eval σ = ℓ) (hHX : HX.eval σ = H)
    (hℓ : 0 < ℓ) :
    (violGen s d iX vX xbX (var (b + 33)) (var (b + 34)) (var (b + 35)) (var (b + 36)) ℓX HX).out
      x σ = [] ↔ c ∈ sc.domain := by
  have hg : ∀ k < 4, (var (b + 33 + k)).eval σ = ((τ.drop (b + 28)).drop 5).getD k 0 := by
    intro k hk
    rw [getD_drop', getD_drop', Xp.eval_var, ← hστ, getD_take' (by omega)]
    congr 1; omega
  have hl : ((τ.drop (b + 28)).drop 5).length = 4 := by simp [hτ]
  have h4 := eq_of_length_four hl
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  rw [violGen_out_eq_nil_iff hσ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hb.1, hb.2.1, hb.2.2.1, show b + 33 < d by omega, show b + 34 < d by omega,
        show b + 35 < d by omega, show b + 36 < d by omega, hb.2.2.2.1, hb.2.2.2.2⟩)
    hi hv hxb (hg 0 (by omega)) (hg 1 (by omega)) (hg 2 (by omega)) (hg 3 (by omega)) hℓX hHX hℓ,
    mem_domain_of_schRec hrec, ← h4]

end Lax119563Proofs.Reduction
