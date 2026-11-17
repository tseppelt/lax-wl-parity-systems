import Lax119563Proofs.Compiler.CStm

/-!
# A calculus for structured statements

`CStm.Good x w c st st' T`: `c` fits (all values below `2 ^ w`, loops terminate), its
denotation maps `st` to `st'`, and its cost is at most `T`. Combinators for all statements;
loops are handled along a sequence of states (`Good.loop`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

namespace CStm

/-- `c` fits, maps `st` to `st'` and costs at most `T`. -/
def Good (x : List Bool) (w : ℕ) (c : CStm R Q) (st st' : NSt R Q) (T : ℕ) : Prop :=
  Fits x w c st ∧ exec x c st = st' ∧ cost x w c st ≤ T

namespace Good

variable {c p q : CStm R Q} {st st' st₁ st₂ st₃ : NSt R Q} {T T' T₁ T₂ : ℕ}

lemma mono (h : Good x w c st st' T) (hT : T ≤ T') : Good x w c st st' T' :=
  ⟨h.1, h.2.1, h.2.2.trans hT⟩

lemma of_eq (h : Good x w c st st₁ T) (hs : st₁ = st₂) (hT : T ≤ T') : Good x w c st st₂ T' :=
  hs ▸ h.mono hT

lemma skip : Good x w (skip : CStm R Q) st st (unitCost w) := ⟨trivial, rfl, le_rfl⟩

lemma set {r : Fin R} {e : Ex R} (h : e.Fits w st.env) :
    Good x w (set r e) st (st.set r (e.eval st.env)) (e.size * Ex.nodeCost w + unitCost w) :=
  ⟨h, rfl, le_rfl⟩

lemma emit {e : Ex R} (h : e.Fits w st.env) :
    Good x w (emit e) st { st with out := st.out ++ [e.eval st.env] }
      (e.size * Ex.nodeCost w + unitCost w) :=
  ⟨h, rfl, le_rfl⟩

lemma push {q : Fin Q} {e : Ex R} (h : e.Fits w st.env) :
    Good x w (push q e : CStm R Q) st (st.setS q (e.eval st.env :: st.stk q))
      (e.size * Ex.nodeCost w + unitCost w) :=
  ⟨h, rfl, le_rfl⟩

lemma pop (q : Fin Q) (r : Fin R) :
    Good x w (pop q r : CStm R Q) st ((st.setS q (st.stk q).tail).set r ((st.stk q).headD 0))
      (unitCost w + 1) :=
  ⟨trivial, rfl, le_rfl⟩

lemma sne (r : Fin R) (q : Fin Q) :
    Good x w (sne r q : CStm R Q) st (st.set r (if (st.stk q).isEmpty then 0 else 1))
      (2 * unitCost w + 1) :=
  ⟨trivial, rfl, le_rfl⟩

lemma rd (r : Fin R) :
    Good x w (rd r : CStm R Q) st
      { (st.set r (inBit x st.pos)) with pos := min (st.pos + 1) x.length } (unitCost w) :=
  ⟨trivial, rfl, le_rfl⟩

lemma rst : Good x w (rst : CStm R Q) st { st with pos := 0 } (unitCost w * (st.pos + 1)) :=
  ⟨trivial, rfl, le_rfl⟩

lemma seq (h₁ : Good x w p st₁ st₂ T₁) (h₂ : Good x w q st₂ st₃ T₂) :
    Good x w (.seq p q) st₁ st₃ (T₁ + T₂) := by
  obtain ⟨f₁, e₁, c₁⟩ := h₁
  obtain ⟨f₂, e₂, c₂⟩ := h₂
  subst e₁
  exact ⟨⟨f₁, f₂⟩, e₂, by simp only [cost]; omega⟩

lemma iteT {e : Ex R} (he : e.Fits w st.env) (hc : e.eval st.env ≠ 0)
    (h : Good x w p st st' T) : Good x w (.ite e p q) st st' (condCost w e + T) := by
  obtain ⟨f, ex, co⟩ := h
  refine ⟨⟨he, by rw [if_pos hc]; exact f⟩, by simp only [exec, if_pos hc]; exact ex, ?_⟩
  simp only [cost, if_pos hc]; omega

lemma iteF {e : Ex R} (he : e.Fits w st.env) (hc : e.eval st.env = 0)
    (h : Good x w q st st' T) : Good x w (.ite e p q) st st' (condCost w e + T) := by
  obtain ⟨f, ex, co⟩ := h
  have hc' : ¬ e.eval st.env ≠ 0 := by simpa using hc
  refine ⟨⟨he, by rw [if_neg hc']; exact f⟩, by simp only [exec, if_neg hc']; exact ex, ?_⟩
  simp only [cost, if_neg hc']; omega

/-- **Loops along a sequence of states.** -/
lemma loop {e : Ex R} {body : CStm R Q} (n : ℕ) (S : ℕ → NSt R Q) (C : ℕ → ℕ)
    (hc : ∀ j < n, e.eval (S j).env ≠ 0) (hn : e.eval (S n).env = 0)
    (hf : ∀ j ≤ n, e.Fits w (S j).env)
    (hb : ∀ j < n, Good x w body (S j) (S (j + 1)) (C j)) :
    Good x w (.loop e body) (S 0) (S n)
      (∑ j ∈ Finset.range n, (C j + condCost w e) + condCost w e) := by
  have hit : ∀ j ≤ n, iter x body (S 0) j = S j := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [iter_succ, ih (by omega), (hb j (by omega)).2.1]
  have hc' : ∀ j < n, e.eval (iter x body (S 0) j).env ≠ 0 := fun j hj => by
    rw [hit j hj.le]; exact hc j hj
  have hn' : e.eval (iter x body (S 0) n).env = 0 := by rw [hit n le_rfl]; exact hn
  refine ⟨⟨n, hn', fun j hj => ⟨hc' j hj, ?_⟩, fun j hj => ?_⟩, ?_, ?_⟩
  · have := hit j hj.le; simp only [iter] at this; rw [this]; exact (hb j hj).1
  · have := hit j hj; simp only [iter] at this; rw [this]; exact hf j hj
  · rw [exec_loop hn' hc', hit n le_rfl]
  · rw [cost_loop hn' hc']
    gcongr with j hj
    rw [hit j (Finset.mem_range.mp hj).le]
    exact (hb j (Finset.mem_range.mp hj)).2.2

/-- Loops with a uniform cost bound per iteration. -/
lemma loop_const {e : Ex R} {body : CStm R Q} (n : ℕ) (S : ℕ → NSt R Q) (C : ℕ)
    (hc : ∀ j < n, e.eval (S j).env ≠ 0) (hn : e.eval (S n).env = 0)
    (hf : ∀ j ≤ n, e.Fits w (S j).env)
    (hb : ∀ j < n, Good x w body (S j) (S (j + 1)) C) :
    Good x w (.loop e body) (S 0) (S n) (n * (C + condCost w e) + condCost w e) :=
  (loop n S (fun _ => C) hc hn hf hb).mono (by simp)

end Good

/-! ## Expression shorthands -/

/-- `[a ≠ 0]`-tests and register expressions. -/
abbrev rv (r : Fin R) : Ex R := .var r

lemma fits_var {env : Fin R → ℕ} {r : Fin R} : (Ex.var r).Fits w env ↔ env r < 2 ^ w := Iff.rfl

end CStm

end Lax119563Proofs.Compiler
