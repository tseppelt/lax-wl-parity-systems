import Lax119563Proofs.Reduction.GLang

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
