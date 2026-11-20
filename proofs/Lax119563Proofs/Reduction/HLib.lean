import Mathlib
import Lax119563Proofs.Reduction.HProg
import Lax119563Proofs.Reduction.Bits

/-!
# A library of register programs

`HLe x w p st st' T`: `p` runs from `st` to `st'` within cost `T`. Derived instructions with
exact specifications: increment (`inc`), counting loops (`forUp`).
-/

namespace Lax119563Proofs.Reduction

variable {R : ℕ} {x : List Bool} {w : ℕ}

/-- `p` runs from `st` to `st'` within cost `T`. -/
def HLe (x : List Bool) (w : ℕ) (p : HProg R) (st st' : HSt R) (T : ℕ) : Prop :=
  ∃ t ≤ T, HRuns x w p st st' t

namespace HLe

variable {p q : HProg R} {st st' st₁ st₂ st₃ : HSt R} {T T' T₁ T₂ : ℕ}

lemma of_runs {t : ℕ} (h : HRuns x w p st st' t) : HLe x w p st st' t := ⟨t, le_rfl, h⟩

lemma mono (h : HLe x w p st st' T) (hT : T ≤ T') : HLe x w p st st' T' := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t, by omega, h⟩

lemma seq (h₁ : HLe x w p st₁ st₂ T₁) (h₂ : HLe x w q st₂ st₃ T₂) :
    HLe x w (.seq p q) st₁ st₃ (T₁ + T₂) := by
  obtain ⟨t₁, ht₁, h₁⟩ := h₁; obtain ⟨t₂, ht₂, h₂⟩ := h₂
  exact ⟨t₁ + t₂, by omega, .seq h₁ h₂⟩

lemma iteT {c} (hc : c st.view = true) (h : HLe x w p st st' T) :
    HLe x w (.ite c p q) st st' (T + 1) := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t + 1, by omega, .iteT hc h⟩

lemma iteF {c} (hc : c st.view = false) (h : HLe x w q st st' T) :
    HLe x w (.ite c p q) st st' (T + 1) := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t + 1, by omega, .iteF hc h⟩

lemma loopF {c} (hc : c st.view = false) : HLe x w (.loop c p) st st 1 := of_runs (.loopF hc)

lemma loopT {c} (hc : c st₁.view = true) (h₁ : HLe x w p st₁ st₂ T₁)
    (h₂ : HLe x w (.loop c p) st₂ st₃ T₂) : HLe x w (.loop c p) st₁ st₃ (T₁ + T₂ + 1) := by
  obtain ⟨t₁, ht₁, h₁⟩ := h₁; obtain ⟨t₂, ht₂, h₂⟩ := h₂
  exact ⟨t₁ + t₂ + 1, by omega, .loopT hc h₁ h₂⟩

lemma of_eq (h : HLe x w p st st₁ T) (hs : st₁ = st₂) (hT : T ≤ T') : HLe x w p st st₂ T' :=
  hs ▸ h.mono hT

/-- A loop along a sequence of states. -/
lemma loop_seq {c} (n : ℕ) (S : ℕ → HSt R) (C : ℕ → ℕ)
    (hc : ∀ k < n, c (S k).view = true) (hn : c (S n).view = false)
    (hb : ∀ k < n, HLe x w p (S k) (S (k + 1)) (C k)) :
    HLe x w (.loop c p) (S 0) (S n) (∑ k ∈ Finset.range n, (C k + 1) + 1) := by
  suffices H : ∀ d m, m + d = n →
      HLe x w (.loop c p) (S m) (S n) (∑ k ∈ Finset.Ico m n, (C k + 1) + 1) by
    simpa using H n 0 (by simp)
  intro d
  induction d with
  | zero => intro m hm; subst hm; simpa using loopF hn
  | succ d ih =>
    intro m hm
    have hlt : m < n := by omega
    refine (loopT (hc m hlt) (hb m hlt) (ih (m + 1) (by omega))).mono (le_of_eq ?_)
    rw [Finset.sum_eq_sum_Ico_succ_bot hlt]; ring

/-- A loop along a sequence of states with a uniform cost bound. -/
lemma loop_seq_const {c} (n : ℕ) (S : ℕ → HSt R) (C : ℕ)
    (hc : ∀ k < n, c (S k).view = true) (hn : c (S n).view = false)
    (hb : ∀ k < n, HLe x w p (S k) (S (k + 1)) C) :
    HLe x w (.loop c p) (S 0) (S n) (n * (C + 1) + 1) := by
  refine (loop_seq n S (fun _ => C) hc hn hb).mono (le_of_eq ?_)
  simp

end HLe

/-! ## Views -/

namespace HSt

lemma view_isSome_iff (st : HSt R) (r : Fin R) : (st.view r).isSome = true ↔ st.env r ≠ 0 := by
  unfold view; split_ifs with h <;> simp [h]

@[simp] lemma set_set_same (st : HSt R) (r : Fin R) (u v : ℕ) :
    (st.set r u).set r v = st.set r v := by
  ext <;> simp [set]

@[simp] lemma set_self (st : HSt R) (r : Fin R) : st.set r (st.env r) = st := by
  ext <;> simp [set]

@[simp] lemma set_env_self (st : HSt R) (r : Fin R) (v : ℕ) : (st.set r v).env r = v := by
  simp [set]

lemma set_env_ne (st : HSt R) {r s : Fin R} (h : s ≠ r) (v : ℕ) : (st.set r v).env s = st.env s := by
  simp [set, Function.update_of_ne h]

end HSt

/-! ## Increment and constants -/

/-- `r := r + 1`, using the scratch register `t` (left at `1`). -/
def HProg.inc (r t : Fin R) : HProg R := .seq (.clr t) (.seq (.one t) (.add r t))

lemma inc_spec {r t : Fin R} (hrt : r ≠ t) {st : HSt R} (ht : st.env t < 2 ^ w)
    (hr : st.env r + 1 < 2 ^ w) :
    HLe x w (HProg.inc r t) st ((st.set t 1).set r (st.env r + 1)) (3 * unitCost w) := by
  have h2 : (1 : ℕ) < 2 ^ w := by omega
  refine ((HLe.of_runs (HRuns.clr ht)).seq ((HLe.of_runs (HRuns.one ?_)).seq
    (HLe.of_runs (HRuns.add hrt ?_)))).of_eq ?_ (by omega)
  · simpa using h2
  · simp [HSt.set_env_ne _ hrt]; omega
  · simp [HSt.set_env_ne _ hrt]

/-! ## Counting loops -/

/-- `for i ∈ [0, lim): body`, with the flag `f` (`[i < lim]`) and the scratch register `t`. -/
def HProg.forUp (i lim f t : Fin R) (body : HProg R) : HProg R :=
  .seq (.clr i) (.seq (.lt f i lim)
    (.loop (fun v => (v f).isSome) (.seq body (.seq (HProg.inc i t) (.lt f i lim)))))

/-- The flag value `[a < b]`. -/
def ltFlag (a b : ℕ) : ℕ := if a < b then 1 else 0

end Lax119563Proofs.Reduction
