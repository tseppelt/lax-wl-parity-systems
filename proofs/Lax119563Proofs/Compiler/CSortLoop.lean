import Lax119563Proofs.Compiler.CStack

/-!
# Loops with a variant

`Good.loop_var`: a loop whose body keeps an invariant, decreases a variant `μ` and costs at
most `K (φ s - φ s') + K₀` for a nonincreasing potential `φ` runs within
`K φ s + μ s (K₀ + condCost) + condCost`. Also `Good.loop_stop`, `Good.loop_cons`.

`moveN src dst cnt i t`: move the top `n` words of `src` onto `dst` (reversed), `n` the value
of `cnt` (`moveN_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

namespace CStm

namespace Good

lemma loop_stop {e : Ex R} {body : CStm R Q} {s : NSt R Q} (he : e.Fits w s.env)
    (h0 : e.eval s.env = 0) : Good x w (.loop e body) s s (condCost w e) :=
  (loop (body := body) 0 (fun _ => s) (fun _ => 0) (fun j hj => absurd hj (by omega)) h0
    (fun _ _ => he) (fun j hj => absurd hj (by omega))).mono (by simp)

lemma loop_cons {e : Ex R} {body : CStm R Q} {s s₁ s' : NSt R Q} {C T : ℕ}
    (he : e.Fits w s.env) (hc : e.eval s.env ≠ 0) (h₁ : Good x w body s s₁ C)
    (h₂ : Good x w (.loop e body) s₁ s' T) :
    Good x w (.loop e body) s s' (C + condCost w e + T) := by
  obtain ⟨⟨n, hn, hlt, hf⟩, hex, hco⟩ := h₂
  have hit : ∀ j, iter x body s (j + 1) = iter x body s₁ j := by
    intro j
    show (exec x body)^[j + 1] s = (exec x body)^[j] s₁
    rw [Function.iterate_succ_apply, h₁.2.1]
  have hn' : e.eval (iter x body s (n + 1)).env = 0 := by rw [hit]; exact hn
  have hlt' : ∀ j < n + 1, e.eval (iter x body s j).env ≠ 0 := by
    intro j hj
    rcases j with _ | j
    · exact hc
    · rw [hit]; exact (hlt j (by omega)).1
  refine ⟨⟨n + 1, hn', fun j hj => ⟨hlt' j hj, ?_⟩, fun j hj => ?_⟩, ?_, ?_⟩
  · rcases j with _ | j
    · exact h₁.1
    · have := hit j; simp only [iter] at this; rw [this]; exact (hlt j (by omega)).2
  · rcases j with _ | j
    · exact he
    · have := hit j; simp only [iter] at this; rw [this]; exact hf j (by omega)
  · rw [exec_loop hn' hlt', hit, ← hex, exec_loop hn (fun j hj => (hlt j hj).1)]
  · rw [cost_loop hn' hlt', Finset.sum_range_succ']
    rw [cost_loop hn (fun j hj => (hlt j hj).1)] at hco
    simp only [hit, iter_zero]
    have := h₁.2.2
    omega

/-- **Loops with a variant and a potential.** -/
lemma loop_var {e : Ex R} {body : CStm R Q} (Inv : NSt R Q → Prop) (μ φ : NSt R Q → ℕ)
    (K K₀ : ℕ)
    (hstep : ∀ s, Inv s → e.Fits w s.env ∧ (e.eval s.env ≠ 0 →
      ∃ s', Good x w body s s' (K * (φ s - φ s') + K₀) ∧ Inv s' ∧ μ s' < μ s ∧ φ s' ≤ φ s)) :
    ∀ s, Inv s → ∃ s', Good x w (.loop e body) s s'
      (K * φ s + μ s * (K₀ + condCost w e) + condCost w e) ∧ Inv s' ∧ e.eval s'.env = 0 := by
  intro s
  induction' hm : μ s using Nat.strong_induction_on with m ih generalizing s
  intro hI
  obtain ⟨hf, hst⟩ := hstep s hI
  by_cases hc : e.eval s.env = 0
  · exact ⟨s, (loop_stop hf hc).mono (by omega), hI, hc⟩
  · obtain ⟨s₁, h₁, hI₁, hμ, hφ⟩ := hst hc
    obtain ⟨s', h', hI', hc'⟩ := ih _ (by omega) s₁ rfl hI₁
    refine ⟨s', (loop_cons hf hc h₁ h').mono ?_, hI', hc'⟩
    have e1 : K * (φ s - φ s₁) + K * φ s₁ = K * φ s := by
      rw [← mul_add, Nat.sub_add_cancel hφ]
    have e2 : μ s₁ * (K₀ + condCost w e) + (K₀ + condCost w e) ≤ m * (K₀ + condCost w e) := by
      rw [← add_one_mul]; exact Nat.mul_le_mul_right _ (by omega)
    omega

end Good

/-! ## Moving words -/

/-- Move the top `cnt` words of `src` onto `dst` (counter `i`, value register `t`). -/
def moveN (src dst : Fin Q) (cnt i t : Fin R) : CStm R Q :=
  .seq (.set i (.const 0))
    (.loop (.lt (rv i) (rv cnt))
      (.seq (.pop src t) (.seq (.push dst (rv t)) (.set i (.add (rv i) (.const 1))))))

/-- The effect of a routine on the rest of the state: cursor, output and all registers
outside `regs` are kept. -/
def Frame (st st' : NSt R Q) (regs : List (Fin R)) : Prop :=
  st'.pos = st.pos ∧ st'.out = st.out ∧ ∀ r ∉ regs, st'.env r = st.env r

lemma Frame.refl (st : NSt R Q) (regs : List (Fin R)) : Frame st st regs :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

lemma Frame.trans {st₁ st₂ st₃ : NSt R Q} {regs : List (Fin R)} (h₁ : Frame st₁ st₂ regs)
    (h₂ : Frame st₂ st₃ regs) : Frame st₁ st₃ regs :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, fun r hr => (h₂.2.2 r hr).trans (h₁.2.2 r hr)⟩

lemma Frame.mono {st st' : NSt R Q} {regs regs' : List (Fin R)} (h : Frame st st' regs)
    (hs : regs ⊆ regs') : Frame st st' regs' :=
  ⟨h.1, h.2.1, fun r hr => h.2.2 r (fun h' => hr (hs h'))⟩

/-- The stacks after moving `n` words from `src` to `dst`. -/
def movedStk (S : Fin Q → List ℕ) (src dst : Fin Q) (n : ℕ) : Fin Q → List ℕ :=
  Function.update (Function.update S src ((S src).drop n)) dst (((S src).take n).reverse ++ S dst)

lemma movedStk_zero (S : Fin Q → List ℕ) (src dst : Fin Q) (h : src ≠ dst) :
    movedStk S src dst 0 = S := by
  funext q; unfold movedStk
  by_cases h1 : q = dst
  · subst h1; simp
  · by_cases h2 : q = src
    · subst h2; simp [Function.update_of_ne h1]
    · simp [Function.update_of_ne h1, Function.update_of_ne h2]

lemma movedStk_src (S : Fin Q → List ℕ) {src dst : Fin Q} (h : src ≠ dst) (n : ℕ) :
    movedStk S src dst n src = (S src).drop n := by
  simp [movedStk, Function.update_of_ne h]

lemma movedStk_dst (S : Fin Q → List ℕ) (src dst : Fin Q) (n : ℕ) :
    movedStk S src dst n dst = ((S src).take n).reverse ++ S dst := by
  simp [movedStk]

lemma movedStk_other (S : Fin Q → List ℕ) {src dst q : Fin Q} (h₁ : q ≠ src) (h₂ : q ≠ dst)
    (n : ℕ) : movedStk S src dst n q = S q := by
  simp [movedStk, Function.update_of_ne h₁, Function.update_of_ne h₂]

lemma Ex.fits_lt {env : Fin R → ℕ} {a b : Ex R} : (Ex.lt a b).Fits w env ↔ a.Fits w env ∧ b.Fits w env :=
  Iff.rfl

lemma moveN_good {src dst : Fin Q} {cnt i t : Fin R} (hsd : src ≠ dst) (hci : cnt ≠ i)
    (hct : cnt ≠ t) (hit : i ≠ t) (st : NSt R Q) {n : ℕ} (hn : st.env cnt = n)
    (hlen : n ≤ (st.stk src).length) (hw : n + 1 < 2 ^ w)
    (hb : ∀ v ∈ (st.stk src).take n, v < 2 ^ w) :
    ∃ st', Good x w (moveN src dst cnt i t) st st' ((n + 1) * (12 * Ex.nodeCost w)) ∧
      st'.stk = movedStk st.stk src dst n ∧ Frame st st' [i, t] := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  -- the loop invariant
  set Inv : NSt R Q → Prop := fun s => s.env i ≤ n ∧ s.env cnt = n ∧
    s.stk = movedStk st.stk src dst (s.env i) ∧ Frame st s [i, t]
  have hloop := Good.loop_var (x := x) (w := w) (e := .lt (rv i) (rv cnt))
    (body := .seq (.pop src t) (.seq (.push dst (rv t)) (.set i (.add (rv i) (.const 1)))))
    Inv (fun s => n - s.env i) (fun _ => 0) 0 (8 * Ex.nodeCost w) (by
      intro s ⟨hi, hc, hs, hf⟩
      refine ⟨⟨by simp only [rv, Ex.Fits]; omega, by simp only [rv, Ex.Fits]; omega⟩, ?_⟩
      intro hcond
      have hlt : s.env i < n := by simpa [rv, Ex.eval, hc] using hcond
      have hsrc : s.stk src = (st.stk src).drop (s.env i) := by rw [hs, movedStk_src _ hsd]
      have hd := List.drop_eq_getElem_cons (show s.env i < (st.stk src).length by omega)
      have hv : (st.stk src)[s.env i] < 2 ^ w :=
        hb _ (List.mem_take_iff_getElem.mpr ⟨s.env i, by simp; omega, rfl⟩)
      refine ⟨_, ((Good.pop src t).seq ((Good.push ?_).seq (Good.set ?_))).mono ?_, ?_,
        ?_, le_rfl⟩
      · simp only [rv, Ex.Fits, NSt.set_env, NSt.setS_env, Function.update_self, hsrc, hd,
          List.headD_cons]
        exact hv
      · simp only [rv, Ex.Fits, Ex.eval, NSt.set_env, NSt.setS_env, Function.update_of_ne hit,
          NSt.setS_env]
        refine ⟨?_, ?_, ?_⟩
        · exact lt_trans hlt (lt_trans (Nat.lt_succ_self n) hw)
        · exact lt_of_le_of_lt (Nat.le_add_left 1 n) hw
        · exact lt_of_le_of_lt (Nat.succ_le_succ hlt.le) hw
      · simp only [rv, Ex.size]; omega
      · simp only [Inv, rv, Ex.eval, NSt.set_env, NSt.setS_env, NSt.set_stk, NSt.setS_stk,
          Function.update_self, Function.update_of_ne hit, Function.update_of_ne hci,
          Function.update_of_ne hct]
        refine ⟨by omega, hc, ?_, ?_⟩
        · rw [hsrc, hd]
          funext q
          simp only [movedStk, List.headD_cons, List.tail_cons]
          by_cases h1 : q = dst
          · subst h1
            simp only [Function.update_self, Function.update_of_ne hsd.symm]
            have ht : (st.stk src).take (s.env i + 1) =
                (st.stk src).take (s.env i) ++ [(st.stk src)[s.env i]] := by
              rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; rfl
            rw [hs, movedStk_dst, ht]
            simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
              List.singleton_append, List.cons_append, List.append_assoc]
          · by_cases h2 : q = src
            · subst h2; simp [Function.update_of_ne h1]
            · simp only [Function.update_of_ne h1, Function.update_of_ne h2]
              rw [hs, movedStk_other _ h2 h1]
        · refine ⟨hf.1, hf.2.1, fun r hr => ?_⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [NSt.set_env, NSt.setS_env, Function.update_of_ne hr.1,
            Function.update_of_ne hr.2]
          exact hf.2.2 r (by simp [hr.1, hr.2])
      · simp only [rv, Ex.eval, NSt.set_env, NSt.setS_env, Function.update_self, Function.update_of_ne hit]; omega)
  have h0 : Good x w (.set i (.const 0) : CStm R Q) st (st.set i 0) (Ex.nodeCost w + unitCost w) :=
    (Good.set (by simp only [Ex.Fits]; omega)).of_eq (by simp [Ex.eval]) (by simp [Ex.size])
  obtain ⟨s', h', ⟨hi', hc', hs', hf'⟩, hend⟩ := hloop (st.set i 0) ⟨by simp, by
    simp [Function.update_of_ne hci, hn], by simp [movedStk_zero _ _ _ hsd], ⟨rfl, rfl, fun r hr => by
      simp at hr; simp [Function.update_of_ne hr.1]⟩⟩
  have hin : s'.env i = n := by
    simp only [rv, Ex.eval, hc'] at hend; split_ifs at hend <;> omega
  refine ⟨s', (h0.seq h').mono ?_, by rw [hs', hin], hf'⟩
  simp only [condCost, rv, Ex.size, Nat.sub_zero, mul_zero, zero_add]
  rw [show st.set i 0 = st.set i 0 from rfl]
  simp only [NSt.set_env, Function.update_self, Nat.sub_zero]
  nlinarith

end CStm

end Lax119563Proofs.Compiler
