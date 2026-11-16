import Lax119563Proofs.Reduction.XLang

/-!
# Specification of compiled expressions

`Xp.spec`: the compiled expression `comp R d A t e` is `Good` (fits, no output, cost at most
`κ w * cost`) and leaves the value of `e` in register `t`, provided the registers below `d`
outside `A` hold the stack and the values fit below `B` with `2 B ≤ 2 ^ w`.
-/

namespace Lax119563Proofs.Reduction

variable {R : ℕ} {x : List Bool} {w : ℕ}

namespace Xp

variable {d : ℕ} {A : List ℕ}

lemma κ_ge (w : ℕ) : 32 * Ex.nodeCost w ≤ κ w ∧ 64 ≤ unitCost w ∧ unitCost w ≤ Ex.nodeCost w :=
  ⟨le_rfl, (nodeCost_ge w).1, (nodeCost_ge w).2⟩

lemma κ_split (w a b : ℕ) : κ w * (a + b) = κ w * a + κ w * b := mul_add _ _ _

/-- The induction hypothesis of `spec`. -/
def SpecAt (x : List Bool) (w B : ℕ) (R d : ℕ) (A : List ℕ) (ρ : List ℕ) (e : Xp) (t : ℕ) :
    Prop :=
  ∀ env : Fin (R + 1) → ℕ, d ≤ t → t + e.need ≤ R →
    (∀ i < d, i ∉ A → env (rg R i) = ρ.getD i 0) → e.Fits B ρ →
    Good x w (comp R d A t e) env [] (κ w * e.cost ρ) ∧
      (Stm.exec x (comp R d A t e) env).1 (rg R t) = e.eval ρ

/-- Two-operand constant-time nodes. -/
lemma spec_bin {B : ℕ} {ρ : List ℕ} (a b : Xp) (op : Ex (R + 1) → Ex (R + 1) → Ex (R + 1))
    (t : ℕ) (env : Fin (R + 1) → ℕ) (iha : SpecAt x w B R d A ρ a t)
    (ihb : SpecAt x w B R d A ρ b (t + 1)) (hdt : d ≤ t)
    (hR : t + max a.need (b.need + 1) ≤ R)
    (henv : ∀ i < d, i ∉ A → env (rg R i) = ρ.getD i 0) (hfa : a.Fits B ρ) (hfb : b.Fits B ρ)
    (hop : ∀ env' : Fin (R + 1) → ℕ, env' (rg R t) = a.eval ρ → env' (rg R (t + 1)) = b.eval ρ →
      Ex.Fits w env' (op (.var (rg R t)) (.var (rg R (t + 1)))) ∧
        (op (.var (rg R t)) (.var (rg R (t + 1)))).size = 3) :
    Good x w (.seq (comp R d A t a) (.seq (comp R d A (t + 1) b)
        (.set (rg R t) (op (.var (rg R t)) (.var (rg R (t + 1))))))) env []
        (κ w * (a.cost ρ + b.cost ρ + 1)) ∧
      ∃ env' : Fin (R + 1) → ℕ, env' (rg R t) = a.eval ρ ∧ env' (rg R (t + 1)) = b.eval ρ ∧
        (Stm.exec x (.seq (comp R d A t a) (.seq (comp R d A (t + 1) b)
          (.set (rg R t) (op (.var (rg R t)) (.var (rg R (t + 1))))))) env).1 (rg R t) =
          Ex.eval env' (op (.var (rg R t)) (.var (rg R (t + 1)))) := by
  have K := κ_ge w
  have h1 := one_le_need b
  obtain ⟨g1, v1⟩ := iha env hdt (by omega) henv hfa
  have henv1 : ∀ i < d, i ∉ A →
      (Stm.exec x (comp R d A t a) env).1 (rg R i) = ρ.getD i 0 := fun i hi hiA => by
    rw [comp_frame a (by omega) (by omega)]; exact henv i hi hiA
  obtain ⟨g2, v2⟩ := ihb _ (by omega) (by omega) henv1 hfb
  have v1' : (Stm.exec x (comp R d A (t + 1) b) (Stm.exec x (comp R d A t a) env).1).1
      (rg R t) = a.eval ρ := by rw [comp_frame b (by omega) (by omega)]; exact v1
  obtain ⟨hf3, hs3⟩ := hop _ v1' v2
  refine ⟨(Good.seq0 g1 (Good.seq0 g2 ((Good.set hf3).of_eq rfl le_rfl))).mono ?_,
    _, v1', v2, ?_⟩
  · rw [hs3, κ_split, κ_split]; omega
  · simp only [exec_seq_fst, exec_set_fst, Function.update_self]

set_option maxHeartbeats 400000 in
lemma spec_mulB {B : ℕ} (hB : 2 * B ≤ 2 ^ w) {ρ : List ℕ} (a b k : Xp) (iha : ∀ t, SpecAt x w B R d A ρ a t) (ihb : ∀ t, SpecAt x w B R d A ρ b t) (ihk : ∀ t, SpecAt x w B R d A ρ k t) (t : ℕ) :
    SpecAt x w B R d A ρ (mulB a b k) t := by
    have K := κ_ge w
    intro env hdt hR henv hf
    obtain ⟨hfa, hfb, hfk, hAK⟩ := hf
    simp only [need] at hR
    have hBv := eval_lt hfb; have hKv := eval_lt hfk
    obtain ⟨g1, v1⟩ := iha (t + 1) env (by omega) (by omega) henv hfa
    set env1 := (Stm.exec x (comp R d A (t + 1) a) env).1 with he1
    obtain ⟨g2, v2⟩ := ihb (t + 2) env1 (by omega) (by omega) (fun i hi hiA => by
      rw [he1, comp_frame a (by omega) (by omega)]; exact henv i hi hiA) hfb
    set env2 := (Stm.exec x (comp R d A (t + 2) b) env1).1 with he2
    obtain ⟨g3, v3⟩ := ihk (t + 3) env2 (by omega) (by omega) (fun i hi hiA => by
      rw [he2, comp_frame b (by omega) (by omega), he1, comp_frame a (by omega) (by omega)]
      exact henv i hi hiA) hfk
    set env3 := (Stm.exec x (comp R d A (t + 3) k) env2).1 with he3
    have w1 : env3 (rg R (t + 1)) = a.eval ρ := by
      rw [he3, comp_frame k (by omega) (by omega), he2, comp_frame b (by omega) (by omega)]
      exact v1
    have w2 : env3 (rg R (t + 2)) = b.eval ρ := by
      rw [he3, comp_frame k (by omega) (by omega)]; exact v2
    set env4 := Function.update env3 (rg R t) 0 with he4
    have n01 := rg_ne (R := R) (t := t) (t' := t + 1) (by omega) (by omega)
    have n02 := rg_ne (R := R) (t := t) (t' := t + 2) (by omega) (by omega)
    have n03 := rg_ne (R := R) (t := t) (t' := t + 3) (by omega) (by omega)
    have n04 := rg_ne (R := R) (t := t) (t' := t + 4) (by omega) (by omega)
    have n12 := rg_ne (R := R) (t := t + 1) (t' := t + 2) (by omega) (by omega)
    have n14 := rg_ne (R := R) (t := t + 1) (t' := t + 4) (by omega) (by omega)
    have n24 := rg_ne (R := R) (t := t + 2) (t' := t + 4) (by omega) (by omega)
    have hL : env4 (rg R (t + 3)) = k.eval ρ := by
      rw [he4, Function.update_of_ne (Ne.symm n03)]; exact v3
    have H := Stm.good_loopInv (x := x) (w := w) (i := rg R (t + 4)) (lim := rg R (t + 3))
      (body := mulBody (rg R t) (rg R (t + 1)) (rg R (t + 2))) (env := env4)
      (fun j e => e (rg R t) = a.eval ρ * (b.eval ρ % 2 ^ j) ∧
        e (rg R (t + 1)) = a.eval ρ * 2 ^ j ∧ e (rg R (t + 2)) = b.eval ρ / 2 ^ j)
      (fun _ => []) (10 * Ex.nodeCost w + 3 * unitCost w + 1) (by rw [hL]; omega)
      ⟨by simp [he4, Nat.mod_one], by rw [he4, Function.update_of_ne (Ne.symm n01), w1]; simp,
        by rw [he4, Function.update_of_ne (Ne.symm n02), w2]; simp⟩ (by
        intro j hj e ⟨h1, h2, h3⟩
        rw [hL] at hj
        have S := mulBody_step (x := x) n01 n02 n12 (Function.update e (rg R (t + 4)) j) hB
          (by rw [Function.update_of_ne n04]; exact h1)
          (by rw [Function.update_of_ne n14]; exact h2)
          (by rw [Function.update_of_ne n24]; exact h3) hj hAK hBv
        exact ⟨S.1, S.2.1, S.2.2.1, S.2.2.2.1⟩)
    rw [hL] at H
    have g4 : Good x w (Stm.set (rg R t) (.const 0)) env3 [] (Ex.nodeCost w + unitCost w) :=
      (Good.set (by simp only [Ex.Fits]; positivity)).of_eq rfl (by simp [Ex.size])
    have hK1 : k.eval ρ * (10 * Ex.nodeCost w + 3 * unitCost w + 1 + 4 * unitCost w + 1) ≤
        k.eval ρ * κ w := Nat.mul_le_mul_left _ (by omega)
    refine ⟨(Good.seq0 g1 (Good.seq0 g2 (Good.seq0 g3 (Good.seq0 g4
      (H.1.of_eq (by simp) le_rfl))))).mono ?_, ?_⟩
    · simp only [cost, κ_split]; rw [Nat.mul_comm (κ w) (k.eval ρ)]; omega
    · have hx : (Stm.exec x (comp R d A t (mulB a b k)) env).1 = (Stm.exec x (Stm.loop
          (rg R (t + 4)) (rg R (t + 3)) (mulBody (rg R t) (rg R (t + 1)) (rg R (t + 2)))) env4).1 :=
        rfl
      rw [hx, Stm.exec_loop_fst, Function.update_of_ne n04, hL, H.2.1]
      rfl

set_option maxHeartbeats 400000 in
lemma spec_shl {B : ℕ} (hB : 2 * B ≤ 2 ^ w) {ρ : List ℕ} (a k : Xp) (iha : ∀ t, SpecAt x w B R d A ρ a t) (ihk : ∀ t, SpecAt x w B R d A ρ k t) (t : ℕ) :
    SpecAt x w B R d A ρ (shl a k) t := by
    have K := κ_ge w
    intro env hdt hR henv hf
    obtain ⟨hfa, hfk, hAK⟩ := hf
    simp only [need] at hR
    have hKv := eval_lt hfk
    obtain ⟨g1, v1⟩ := iha t env hdt (by omega) henv hfa
    set env1 := (Stm.exec x (comp R d A t a) env).1 with he1
    obtain ⟨g2, v2⟩ := ihk (t + 1) env1 (by omega) (by omega) (fun i hi hiA => by
      rw [he1, comp_frame a (by omega) (by omega)]; exact henv i hi hiA) hfk
    set env2 := (Stm.exec x (comp R d A (t + 1) k) env1).1 with he2
    have w1 : env2 (rg R t) = a.eval ρ := by
      rw [he2, comp_frame k (by omega) (by omega)]; exact v1
    have n01 := rg_ne (R := R) (t := t) (t' := t + 1) (by omega) (by omega)
    have n02 := rg_ne (R := R) (t := t) (t' := t + 2) (by omega) (by omega)
    have n12 := rg_ne (R := R) (t := t + 1) (t' := t + 2) (by omega) (by omega)
    have g3 := shlS_good (x := x) (Ne.symm n02) (Ne.symm n01) (Ne.symm n12) hB
      (env := env2) (by rw [v2]; exact hKv) (by rw [w1, v2]; exact hAK)
    rw [v2] at g3
    have hK1 : k.eval ρ * (3 * Ex.nodeCost w + 5 * unitCost w + 1) ≤ k.eval ρ * κ w :=
      Nat.mul_le_mul_left _ (by omega)
    refine ⟨(Good.seq0 g1 (Good.seq0 g2 g3)).mono ?_, ?_⟩
    · simp only [cost, κ_split]; rw [Nat.mul_comm (κ w) (k.eval ρ)]; omega
    · simp only [comp, exec_seq_fst]
      rw [(Stm.exec_shlS (x := x) (Ne.symm n02) (Ne.symm n01) env2).1, w1, v2]; rfl

set_option maxHeartbeats 400000 in
lemma spec_shr {B : ℕ} (hB : 2 * B ≤ 2 ^ w) {ρ : List ℕ} (a k : Xp) (iha : ∀ t, SpecAt x w B R d A ρ a t) (ihk : ∀ t, SpecAt x w B R d A ρ k t) (t : ℕ) :
    SpecAt x w B R d A ρ (shr a k) t := by
    have K := κ_ge w
    intro env hdt hR henv hf
    obtain ⟨hfa, hfk⟩ := hf
    simp only [need] at hR
    have hKv := eval_lt hfk
    have hAv := eval_lt hfa
    obtain ⟨g1, v1⟩ := iha t env hdt (by omega) henv hfa
    set env1 := (Stm.exec x (comp R d A t a) env).1 with he1
    obtain ⟨g2, v2⟩ := ihk (t + 1) env1 (by omega) (by omega) (fun i hi hiA => by
      rw [he1, comp_frame a (by omega) (by omega)]; exact henv i hi hiA) hfk
    set env2 := (Stm.exec x (comp R d A (t + 1) k) env1).1 with he2
    have w1 : env2 (rg R t) = a.eval ρ := by
      rw [he2, comp_frame k (by omega) (by omega)]; exact v1
    have n01 := rg_ne (R := R) (t := t) (t' := t + 1) (by omega) (by omega)
    have n02 := rg_ne (R := R) (t := t) (t' := t + 2) (by omega) (by omega)
    have n12 := rg_ne (R := R) (t := t + 1) (t' := t + 2) (by omega) (by omega)
    have g3 := shrS_good (x := x) (Ne.symm n02) (Ne.symm n01) (Ne.symm n12) hB
      (env := env2) (by rw [v2]; exact hKv) (by rw [w1]; exact hAv)
    rw [v2] at g3
    have hK1 : k.eval ρ * (2 * Ex.nodeCost w + 5 * unitCost w + 1) ≤ k.eval ρ * κ w :=
      Nat.mul_le_mul_left _ (by omega)
    refine ⟨(Good.seq0 g1 (Good.seq0 g2 g3)).mono ?_, ?_⟩
    · simp only [cost, κ_split]; rw [Nat.mul_comm (κ w) (k.eval ρ)]; omega
    · simp only [comp, exec_seq_fst]
      rw [(Stm.exec_shrS (x := x) (Ne.symm n02) (Ne.symm n01) env2).1, w1, v2]; rfl

/-- Distinct registers `t, …, t + 5`. -/
structure Regs6 (R t : ℕ) : Prop where
  n10 : rg R (t + 1) ≠ rg R t
  n12 : rg R (t + 1) ≠ rg R (t + 2)
  n14 : rg R (t + 1) ≠ rg R (t + 4)
  n15 : rg R (t + 1) ≠ rg R (t + 5)
  n20 : rg R (t + 2) ≠ rg R t
  n24 : rg R (t + 2) ≠ rg R (t + 4)
  n25 : rg R (t + 2) ≠ rg R (t + 5)
  n04 : rg R t ≠ rg R (t + 4)
  n05 : rg R t ≠ rg R (t + 5)
  n45 : rg R (t + 4) ≠ rg R (t + 5)
  n31 : rg R (t + 3) ≠ rg R (t + 1)
  n32 : rg R (t + 3) ≠ rg R (t + 2)
  n30 : rg R (t + 3) ≠ rg R t
  n34 : rg R (t + 3) ≠ rg R (t + 4)
  n35 : rg R (t + 3) ≠ rg R (t + 5)

lemma regs6 {R t : ℕ} (h : t + 6 ≤ R) : Regs6 R t :=
  ⟨rg_ne (by omega) (by omega), rg_ne (by omega) (by omega), rg_ne (by omega) (by omega),
    rg_ne (by omega) (by omega), rg_ne (by omega) (by omega), rg_ne (by omega) (by omega),
    rg_ne (by omega) (by omega), rg_ne (by omega) (by omega), rg_ne (by omega) (by omega),
    rg_ne (by omega) (by omega), rg_ne (by omega) (by omega), rg_ne (by omega) (by omega),
    rg_ne (by omega) (by omega), rg_ne (by omega) (by omega), rg_ne (by omega) (by omega)⟩

set_option maxHeartbeats 400000 in
lemma spec_xorM {B : ℕ} (hB : 2 * B ≤ 2 ^ w) {ρ : List ℕ} (a b k : Xp) (iha : ∀ t, SpecAt x w B R d A ρ a t) (ihb : ∀ t, SpecAt x w B R d A ρ b t) (ihk : ∀ t, SpecAt x w B R d A ρ k t) (t : ℕ) :
    SpecAt x w B R d A ρ (xorM a b k) t := by
    have K := κ_ge w
    intro env hdt hR henv hf
    obtain ⟨hfa, hfb, hfk, hK⟩ := hf
    simp only [need] at hR
    have hAv := eval_lt hfa; have hBv := eval_lt hfb
    have hn := regs6 (R := R) (t := t) (by omega)
    obtain ⟨g1, v1⟩ := iha (t + 1) env (by omega) (by omega) henv hfa
    set env1 := (Stm.exec x (comp R d A (t + 1) a) env).1 with he1
    obtain ⟨g2, v2⟩ := ihb (t + 2) env1 (by omega) (by omega) (fun i hi hiA => by
      rw [he1, comp_frame a (by omega) (by omega)]; exact henv i hi hiA) hfb
    set env2 := (Stm.exec x (comp R d A (t + 2) b) env1).1 with he2
    obtain ⟨g3, v3⟩ := ihk (t + 3) env2 (by omega) (by omega) (fun i hi hiA => by
      rw [he2, comp_frame b (by omega) (by omega), he1, comp_frame a (by omega) (by omega)]
      exact henv i hi hiA) hfk
    set env3 := (Stm.exec x (comp R d A (t + 3) k) env2).1 with he3
    have w1 : env3 (rg R (t + 1)) = a.eval ρ := by
      rw [he3, comp_frame k (by omega) (by omega), he2, comp_frame b (by omega) (by omega)]
      exact v1
    have w2 : env3 (rg R (t + 2)) = b.eval ρ := by
      rw [he3, comp_frame k (by omega) (by omega)]; exact v2
    have g4 := xorS_good (x := x) hn.n12 hn.n10 hn.n14 hn.n15 hn.n20 hn.n24 hn.n25 hn.n04 hn.n05 hn.n45 hn.n31 hn.n32 hn.n30 hn.n34 hn.n35 hB
      (env := env3) (by rw [w1]; exact hAv) (by rw [w2]; exact hBv) (by rw [v3]; exact hK)
    rw [v3] at g4
    have hK1 : k.eval ρ * (16 * Ex.nodeCost w + 8 * unitCost w + 2) ≤ k.eval ρ * κ w :=
      Nat.mul_le_mul_left _ (by omega)
    refine ⟨(Good.seq0 g1 (Good.seq0 g2 (Good.seq0 g3 g4))).mono ?_, ?_⟩
    · simp only [cost, κ_split]; rw [Nat.mul_comm (κ w) (k.eval ρ)]; omega
    · have hx : (Stm.exec x (comp R d A t (xorM a b k)) env).1 = (Stm.exec x (Stm.xorS
          (rg R (t + 1)) (rg R (t + 2)) (rg R t) (rg R (t + 4)) (rg R (t + 5)) (rg R (t + 3)))
          env3).1 := rfl
      rw [hx, (Stm.exec_xorS (x := x) hn.n12 hn.n10 hn.n14 hn.n15 hn.n20 hn.n24 hn.n25 hn.n04 hn.n05 hn.n45 hn.n31 hn.n32 hn.n30 hn.n34
        env3).1]
      rw [w1, w2, v3]; rfl

/-- **Specification of compiled expressions.** -/
theorem spec {B : ℕ} (hB : 2 * B ≤ 2 ^ w) {ρ : List ℕ} (hρ : ρ.length = d)
    (hA : ∀ i ∈ A, ρ.getD i 0 = 0) (e : Xp) : ∀ t : ℕ, SpecAt x w B R d A ρ e t := by
  have K := κ_ge w
  intro t
  induction e generalizing t with
  | var i =>
    intro env hdt hR henv hf
    simp only [comp]
    split_ifs with hi
    · refine ⟨(Good.set ?_).of_eq rfl (by simp [Ex.size, cost]; omega), ?_⟩
      · simp only [Ex.Fits]; rw [henv i hi.1 hi.2]; have : ρ.getD i 0 < B := hf; omega
      · simp only [exec_set_fst, Function.update_self, Ex.eval, eval]; exact henv i hi.1 hi.2
    · refine ⟨(Good.set ?_).of_eq rfl (by simp [Ex.size, cost]; omega), ?_⟩
      · simp only [Ex.Fits]; positivity
      · simp only [exec_set_fst, Function.update_self, Ex.eval, eval]
        rcases not_and_or.mp hi with hi | hi
        · rw [List.getD_eq_default _ _ (by omega)]
        · rw [hA i (not_not.mp hi)]
  | const c =>
    intro env hdt hR henv hf
    refine ⟨(Good.set ?_).of_eq rfl (by simp [Ex.size, cost]; omega), ?_⟩
    · simp only [Ex.Fits]; have : c < B := hf; omega
    · simp [comp, exec_set_fst, Ex.eval, eval]
  | add a b iha ihb =>
    intro env hdt hR henv hf
    obtain ⟨hfa, hfb, hs⟩ := hf
    have ha := eval_lt hfa; have hb := eval_lt hfb
    obtain ⟨g, env', e1, e2, hv⟩ := spec_bin a b Ex.add t env (iha t) (ihb (t + 1)) hdt hR henv
      hfa hfb (fun env' h1 h2 => ⟨by simp only [Ex.Fits, Ex.eval, h1, h2]; omega, rfl⟩)
    exact ⟨g, by rw [comp, hv]; simp [Ex.eval, e1, e2, eval]⟩
  | lt a b iha ihb =>
    intro env hdt hR henv hf
    obtain ⟨hfa, hfb⟩ := hf
    have ha := eval_lt hfa; have hb := eval_lt hfb
    obtain ⟨g, env', e1, e2, hv⟩ := spec_bin a b Ex.lt t env (iha t) (ihb (t + 1)) hdt hR henv
      hfa hfb (fun env' h1 h2 => ⟨by simp only [Ex.Fits, h1, h2]; omega, rfl⟩)
    exact ⟨g, by rw [comp, hv]; simp [Ex.eval, e1, e2, eval]⟩
  | half a iha =>
    intro env hdt hR henv hf
    obtain ⟨g1, v1⟩ := iha t env hdt hR henv hf
    have ha := eval_lt (e := a) hf
    refine ⟨(Good.seq0 g1 ((Good.set ?_).of_eq rfl le_rfl)).mono ?_, ?_⟩
    · simp only [Ex.Fits, v1]; omega
    · simp only [Ex.size, cost, κ_split]; omega
    · simp [comp, exec_seq_fst, exec_set_fst, Ex.eval, v1, eval]
  | odd a iha =>
    intro env hdt hR henv hf
    obtain ⟨g1, v1⟩ := iha t env hdt hR henv hf
    have ha := eval_lt (e := a) hf
    refine ⟨(Good.seq0 g1 ((Good.set ?_).of_eq rfl le_rfl)).mono ?_, ?_⟩
    · simp only [Ex.Fits, v1]; omega
    · simp only [Ex.size, cost, κ_split]; omega
    · simp [comp, exec_seq_fst, exec_set_fst, Ex.eval, v1, eval]
  | mulB a b k iha ihb ihk => exact spec_mulB hB a b k iha ihb ihk t
  | shl a k iha ihk => exact spec_shl hB a k iha ihk t
  | shr a k iha ihk => exact spec_shr hB a k iha ihk t
  | xorM a b k iha ihb ihk => exact spec_xorM hB a b k iha ihb ihk t

/-! ## Well-formedness and depth -/

lemma depth_comp (e : Xp) : ∀ t, (comp R d A t e).depth ≤ 3 := by
  induction e with
  | var i => intro t; simp only [comp]; split_ifs <;> simp [Stm.depth, Ex.depth]
  | const c => intro t; simp [comp, Stm.depth, Ex.depth]
  | add a b iha ihb =>
    intro t; have := iha t; have := ihb (t + 1)
    simp only [comp, Stm.depth, Ex.depth]; omega
  | lt a b iha ihb =>
    intro t; have := iha t; have := ihb (t + 1)
    simp only [comp, Stm.depth, Ex.depth]; omega
  | half a iha => intro t; have := iha t; simp only [comp, Stm.depth, Ex.depth]; omega
  | odd a iha => intro t; have := iha t; simp only [comp, Stm.depth, Ex.depth]; omega
  | mulB a b k iha ihb ihk =>
    intro t; have := iha (t + 1); have := ihb (t + 2); have := ihk (t + 3)
    simp only [comp, mulBody, Stm.depth, Ex.depth]; omega
  | shl a k iha ihk =>
    intro t; have := iha t; have := ihk (t + 1)
    simp only [comp, Stm.shlS, Stm.depth, Ex.depth]; omega
  | shr a k iha ihk =>
    intro t; have := iha t; have := ihk (t + 1)
    simp only [comp, Stm.shrS, Stm.depth, Ex.depth]; omega
  | xorM a b k iha ihb ihk =>
    intro t; have := iha (t + 1); have := ihb (t + 2); have := ihk (t + 3)
    simp only [comp, Stm.xorS, xorBody, Stm.depth, Ex.depth]; omega

lemma noX_comp (e : Xp) : ∀ t, (comp R d A t e).noX = true := by
  induction e with
  | var i => intro t; simp only [comp]; split_ifs <;> rfl
  | const c => intro t; rfl
  | add a b iha ihb => intro t; simp [comp, Stm.noX, iha, ihb]
  | lt a b iha ihb => intro t; simp [comp, Stm.noX, iha, ihb]
  | half a iha => intro t; simp [comp, Stm.noX, iha]
  | odd a iha => intro t; simp [comp, Stm.noX, iha]
  | mulB a b k iha ihb ihk => intro t; simp [comp, Stm.noX, iha, ihb, ihk, mulBody]
  | shl a k iha ihk => intro t; simp [comp, Stm.noX, iha, ihk, Stm.shlS]
  | shr a k iha ihk => intro t; simp [comp, Stm.noX, iha, ihk, Stm.shrS]
  | xorM a b k iha ihb ihk => intro t; simp [comp, Stm.noX, iha, ihb, ihk, Stm.xorS, xorBody]

lemma wf_comp (e : Xp) : ∀ t, t + e.need ≤ R → (comp R d A t e).WF := by
  induction e with
  | var i => intro t _; simp only [comp]; split_ifs <;> trivial
  | const c => intro t _; trivial
  | add a b iha ihb =>
    intro t h; simp only [need] at h
    exact ⟨iha t (by omega), ihb (t + 1) (by omega), trivial⟩
  | lt a b iha ihb =>
    intro t h; simp only [need] at h
    exact ⟨iha t (by omega), ihb (t + 1) (by omega), trivial⟩
  | half a iha => intro t h; exact ⟨iha t h, trivial⟩
  | odd a iha => intro t h; exact ⟨iha t h, trivial⟩
  | mulB a b k iha ihb ihk =>
    intro t h; simp only [need] at h
    have n0 : rg R (t + 4) ≠ rg R t := rg_ne (by omega) (by omega)
    have n1 : rg R (t + 4) ≠ rg R (t + 1) := rg_ne (by omega) (by omega)
    have n2 : rg R (t + 4) ≠ rg R (t + 2) := rg_ne (by omega) (by omega)
    have n3 : rg R (t + 4) ≠ rg R (t + 3) := rg_ne (by omega) (by omega)
    have m0 : rg R (t + 3) ≠ rg R t := rg_ne (by omega) (by omega)
    have m1 : rg R (t + 3) ≠ rg R (t + 1) := rg_ne (by omega) (by omega)
    have m2 : rg R (t + 3) ≠ rg R (t + 2) := rg_ne (by omega) (by omega)
    refine ⟨iha _ (by omega), ihb _ (by omega), ihk _ (by omega), trivial, n3, ?_, ?_,
      ⟨trivial, trivial⟩, trivial⟩
    · simp [mulBody, Stm.wr, n0, n1, n2]
    · simp [mulBody, Stm.wr, m0, m1, m2]
  | shl a k iha ihk =>
    intro t h; simp only [need] at h
    have n0 : rg R (t + 2) ≠ rg R t := rg_ne (by omega) (by omega)
    have n1 : rg R (t + 2) ≠ rg R (t + 1) := rg_ne (by omega) (by omega)
    have m0 : rg R (t + 1) ≠ rg R t := rg_ne (by omega) (by omega)
    exact ⟨iha _ (by omega), ihk _ (by omega), n1, by simp [Stm.wr, n0],
      by simp [Stm.wr, m0], trivial⟩
  | shr a k iha ihk =>
    intro t h; simp only [need] at h
    have n0 : rg R (t + 2) ≠ rg R t := rg_ne (by omega) (by omega)
    have n1 : rg R (t + 2) ≠ rg R (t + 1) := rg_ne (by omega) (by omega)
    have m0 : rg R (t + 1) ≠ rg R t := rg_ne (by omega) (by omega)
    exact ⟨iha _ (by omega), ihk _ (by omega), n1, by simp [Stm.wr, n0],
      by simp [Stm.wr, m0], trivial⟩
  | xorM a b k iha ihb ihk =>
    intro t h; simp only [need] at h
    have hn := regs6 (R := R) (t := t) (by omega)
    refine ⟨iha _ (by omega), ihb _ (by omega), ihk _ (by omega), trivial, trivial,
      Ne.symm hn.n35, ?_, ?_, ⟨⟨trivial, trivial⟩, trivial, trivial, trivial⟩⟩
    · simp [xorBody, Stm.wr, Ne.symm hn.n15, Ne.symm hn.n25, Ne.symm hn.n05, Ne.symm hn.n45]
    · simp [xorBody, Stm.wr, hn.n31, hn.n32, hn.n30, hn.n34]

end Xp

end Lax119563Proofs.Reduction
