import Lax119563Proofs.Reduction.CostWF
import Lax119563Proofs.Reduction.CostPassBase
import Lax119563Proofs.Reduction.CostGlob

/-!
# The prelude: computing the globals

`prelude M s C₀ g` pushes the 14 globals `globs M x s ℓ H` (for `ℓ = timeWidth C₀ |x|`,
`H = timeHorizon s C₀ |x|`) and runs `g` on them (**`out_prelude`**, for `s ≥ 2`):
`|x|` (`len`), `log₂ |x|` (`log`), `ℓ`, `H`, `R`, `N = 16 C^3 R^2` (`C = cM M`) by expressions, the command
count `r` and the schema count `Ec` by counting runs of the command enumerator, the codes of
`query` (`2`) and `accept` (`0`), the number `E` of schemas by a counting run of the schema
enumerator, `W, det` by expressions and `2^ℓ` as
`min (2^ℓ) (2^(C₀+4) (|x| + 1))` (so that it is of class `P 1 0`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs

namespace Gn

end Gn

/-! ## Steps -/

section Steps

variable {x : List Bool} {G : List ℕ}

lemma take_succ_getD {k : ℕ} (hk : k < G.length) : G.take k ++ [G.getD k 0] = G.take (k + 1) := by
  rw [List.take_succ, List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk]
  rfl

lemma out_bind_step {k : ℕ} (hk : k < G.length) {e : Xp} {g : Gn}
    (he : e.eval (G.take k) = G.getD k 0) :
    (Gn.bind e g).out x (G.take k) = g.out x (G.take (k + 1)) := by
  simp only [Gn.out, he, take_succ_getD hk]

lemma out_count_step {k : ℕ} (hk : k < G.length) {g h : Gn}
    (hl : (g.out x (G.take k ++ [0])).length = G.getD k 0) :
    (Gn.count g h).out x (G.take k) = h.out x (G.take (k + 1)) := by
  simp only [Gn.out, hl, take_succ_getD hk]

lemma getD_take_lt {l : List ℕ} {i k : ℕ} (h : i < k) : (l.take k).getD i 0 = l.getD i 0 :=
  getD_take' h

lemma getD_take_app {l : List ℕ} {i k : ℕ} (h : i < k) (hk : k ≤ l.length) (a : ℕ) :
    (l.take k ++ [a]).getD i 0 = l.getD i 0 := by
  rw [List.getD_append _ _ _ _ (by simp; omega), getD_take' h]

end Steps

/-! ## Values -/

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

lemma Iv_numLocations :
    (Iv M x s ℓ H).numLocations = numLoc M H + (verifierCmds' M x s ℓ H).length * 8 + 4 := by
  have hc : (APv M x s ℓ H).commands.length = (verifierCmds' M x s ℓ H).length := by
    simp only [AP_commands]; exact List.length_map _
  show (APv M x s ℓ H).numLocations + (APv M x s ℓ H).commands.length * 8 + 4 = _
  rw [hc]
  rfl

lemma code_query_val : (Loc.code (Loc.query : Loc M H)).val = 2 := by
  simp [Loc.code, Loc.tuple, pack]

lemma code_accept_val : (Loc.code (Loc.accept : Loc M H)).val = 0 := by
  simp [Loc.code, Loc.tuple, pack]

lemma sum_map_forall₂ {α β : Type} {R : α → β → Prop} {f : α → ℕ} {g : β → ℕ} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → (∀ a b, R a b → f a = g b) →
      (l₁.map f).sum = (l₂.map g).sum
  | _, _, .nil, _ => rfl
  | _, _, .cons h t, hf => by
    simp only [List.map_cons, List.sum_cons, hf _ _ h, sum_map_forall₂ t hf]

lemma length_flatMap_emit {α : Type} (l : List α) (f : α → List ℕ) (hf : ∀ a, (f a).length = 1) :
    (l.flatMap f).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [hf a, ih]; omega

/-! ## Fits, cost and well-formedness -/

lemma Gn.wfx_len {g : Gn} (h : WFX g) : WFX (len g) := h

end Lax119563Proofs.Reduction
