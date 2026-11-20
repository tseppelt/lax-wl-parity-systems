import Lax119563Proofs.Reduction.SStm
import Lax119563Proofs.Reduction.HMachine

/-!
# Reasoning about structured statements

`Good x w c env out T`: from the valuation `env`, the statement `c` fits into words of `w` bits,
emits `out` and costs at most `T`. Compositional rules for all statements; for loops, the
iteration `k` is described by any valuation with counter `k` that agrees with the initial
valuation on the registers the body does not write (`good_loop`, `good_loopX`).

`Stm.computesWithin`: a well-formed statement that is good from the zero valuation gives a
deterministic machine computing `encodeNats out`.
-/

open Lax119563.BinaryEncodings Lax119563.DeterministicTime

namespace Lax119563Proofs.Reduction

variable {R : ℕ} {x : List Bool} {w : ℕ}

namespace Stm

/-! ## Frames -/

lemma runLoop_frame {f : ℕ → (Fin R → ℕ) → (Fin R → ℕ) × List ℕ} {q : Fin R}
    (hf : ∀ k e, (f k e).1 q = e q) : ∀ k env, (runLoop f k env).1 q = env q
  | 0, _ => rfl
  | k + 1, env => by simp only [runLoop]; rw [hf, runLoop_frame hf k env]

lemma runLoop_out (f : ℕ → (Fin R → ℕ) → (Fin R → ℕ) × List ℕ) : ∀ L env,
    (runLoop f L env).2 = (List.range L).flatMap fun k => (f k (runLoop f k env).1).2
  | 0, _ => rfl
  | L + 1, env => by
    simp only [runLoop]
    rw [runLoop_out f L env, List.range_succ, List.flatMap_append, List.flatMap_singleton]

lemma exec_frame : ∀ (c : Stm R) (env : Fin R → ℕ) (q : Fin R), wr c q = false →
    (exec x c env).1 q = env q
  | skip, _, _, _ => rfl
  | set r e, env, q, h => by
    simp only [wr, decide_eq_false_iff_not] at h; simp [exec, Function.update_of_ne h]
  | emit _, _, _, _ => rfl
  | seq p p', env, q, h => by
    simp only [wr, Bool.or_eq_false_iff] at h
    simp only [exec]; rw [exec_frame p' _ q h.2, exec_frame p env q h.1]
  | ite c p p', env, q, h => by
    simp only [wr, Bool.or_eq_false_iff] at h
    simp only [exec]; split_ifs
    · exact exec_frame p env q h.1
    · exact exec_frame p' env q h.2
  | loop i lim body, env, q, h => by
    simp only [wr, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    simp only [exec, Function.update_of_ne h.1]
    exact runLoop_frame (fun k e => by
      rw [exec_frame body _ q h.2, Function.update_of_ne h.1]) _ env
  | loopX i lim xb body, env, q, h => by
    simp only [wr, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    simp only [exec, Function.update_of_ne h.1.1]
    exact runLoop_frame (fun k e => by
      rw [exec_frame body _ q h.2, Function.update_of_ne h.1.2, Function.update_of_ne h.1.1]) _ env
  | len r, env, q, h => by
    simp only [wr, decide_eq_false_iff_not] at h; simp [exec, Function.update_of_ne h]

/-- An invariant of the valuations of a loop. -/
lemma runLoop_inv {f : ℕ → (Fin R → ℕ) → (Fin R → ℕ) × List ℕ} (Inv : ℕ → (Fin R → ℕ) → Prop)
    {L : ℕ} {env : Fin R → ℕ} (h0 : Inv 0 env)
    (hs : ∀ k < L, ∀ e, Inv k e → Inv (k + 1) (f k e).1) : ∀ k ≤ L, Inv k (runLoop f k env).1
  | 0, _ => h0
  | k + 1, hk => hs k (by omega) _ (runLoop_inv Inv h0 hs k (by omega))

end Stm

/-! ## Good statements -/

/-- From `env`, the statement fits into `w` bits, emits `out` and costs at most `T`. -/
structure Good (x : List Bool) (w : ℕ) (c : Stm R) (env : Fin R → ℕ) (out : List ℕ) (T : ℕ) :
    Prop where
  fits : c.Fits x w env
  out_eq : (c.exec x env).2 = out
  cost_le : c.cost x w env ≤ T

namespace Good

open Stm

variable {c p q : Stm R} {env : Fin R → ℕ} {out out' : List ℕ} {T T' : ℕ}

lemma mono (h : Good x w c env out T) (hT : T ≤ T') : Good x w c env out T' :=
  ⟨h.fits, h.out_eq, h.cost_le.trans hT⟩

lemma of_eq (h : Good x w c env out T) (ho : out = out') (hT : T ≤ T') :
    Good x w c env out' T' := ho ▸ h.mono hT

lemma skip : Good x w (Stm.skip : Stm R) env [] (unitCost w) := ⟨trivial, rfl, le_rfl⟩

lemma set {r : Fin R} {e : Ex R} (h : e.Fits w env) :
    Good x w (Stm.set r e) env [] (e.size * Ex.nodeCost w + unitCost w) := ⟨h, rfl, le_rfl⟩

lemma emit {e : Ex R} (h : e.Fits w env) :
    Good x w (Stm.emit e) env [e.eval env] (e.size * Ex.nodeCost w + unitCost w) :=
  ⟨h, rfl, le_rfl⟩

lemma seq {o₁ o₂ : List ℕ} {T₁ T₂ : ℕ} (h₁ : Good x w p env o₁ T₁)
    (h₂ : Good x w q (p.exec x env).1 o₂ T₂) : Good x w (Stm.seq p q) env (o₁ ++ o₂) (T₁ + T₂) :=
  ⟨⟨h₁.fits, h₂.fits⟩, by simp [exec, h₁.out_eq, h₂.out_eq],
    by simp only [cost]; exact Nat.add_le_add h₁.cost_le h₂.cost_le⟩

lemma iteT {e : Ex R} (he : e.Fits w env) (hc : e.eval env ≠ 0) (h : Good x w p env out T) :
    Good x w (Stm.ite e p q) env out (e.size * Ex.nodeCost w + 1 + T) :=
  ⟨⟨he, by rw [if_pos hc]; exact h.fits⟩, by simp only [exec, if_pos hc]; exact h.out_eq,
    by simp only [cost, if_pos hc]; have := h.cost_le; omega⟩

lemma iteF {e : Ex R} (he : e.Fits w env) (hc : e.eval env = 0) (h : Good x w q env out T) :
    Good x w (Stm.ite e p q) env out (e.size * Ex.nodeCost w + 1 + T) :=
  ⟨⟨he, by rw [if_neg (by simpa using hc)]; exact h.fits⟩,
    by simp only [exec, if_neg (show ¬ e.eval env ≠ 0 by simpa using hc)]; exact h.out_eq,
    by simp only [cost, if_neg (show ¬ e.eval env ≠ 0 by simpa using hc)]; have := h.cost_le; omega⟩

lemma len {r : Fin R} (h : x.length + 1 < 2 ^ w) :
    Good x w (Stm.len r) env []
      (3 * unitCost w + x.length * (4 * unitCost w + 1) + 1 + unitCost w * (x.length + 1)) :=
  ⟨h, rfl, le_rfl⟩

end Good

/-! ## Machines of statements -/

/-- **Machines of statements.** A well-formed statement that is good from the zero valuation
gives a machine computing the code of its output. -/
theorem Stm.computesWithin {D : ℕ} {c : Stm R} {out : List ℕ} {T : ℕ} (hw : 2 ≤ w)
    (hwf : c.WF) (hd : c.depth ≤ D) (h : Good x w c (fun _ => 0) out T)
    (hlen : x.length ≤ (encodeNats out).length) :
    ComputesWithin (c.code R D).machine x (encodeNats out)
      (T + 20 * (encodeNats out).length + 4) := by
  have hb : (⟨fun _ => 0, 0, []⟩ : HSt (R + D + 1)).Bdd w := fun _ => by positivity
  obtain ⟨st', ⟨t, ht, hrun⟩, -, ho, hp⟩ := Stm.code_spec (x := x) hw c (fun _ => 0)
    ⟨fun _ => 0, 0, []⟩ hwf hd h.fits rfl hb (by simp) (Or.inr rfl)
  have ho' : st'.out = out := by rw [ho, h.out_eq]; rfl
  have := HProg.computesWithin hrun hp (by rw [ho']; exact hlen)
  rw [ho'] at this
  exact ComputesWithin.mono this (by have := h.cost_le; omega)

end Lax119563Proofs.Reduction
