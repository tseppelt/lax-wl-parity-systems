import Mathlib
import Lax119563Proofs.Reduction.HProg
import Lax119563Proofs.Reduction.Bits

/-!
# A library of register programs

`HLe x w p st st' T`: `p` runs from `st` to `st'` within cost `T`. Derived instructions with
exact specifications: increment (`inc`), constants (`setC`), counting loops (`forUp`).
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

lemma view_zero {st : HSt R} {r : Fin R} (h : st.env r = 0) : st.view r = none := by
  simp [view, h]

lemma view_ne_zero {st : HSt R} {r : Fin R} (h : st.env r ≠ 0) : (st.view r).isSome := by
  simp [view, h]

lemma view_isSome_iff (st : HSt R) (r : Fin R) : (st.view r).isSome = true ↔ st.env r ≠ 0 := by
  unfold view; split_ifs with h <;> simp [h]

@[simp] lemma set_set_same (st : HSt R) (r : Fin R) (u v : ℕ) :
    (st.set r u).set r v = st.set r v := by
  ext <;> simp [set]

lemma set_comm (st : HSt R) {r s : Fin R} (h : r ≠ s) (u v : ℕ) :
    (st.set r u).set s v = (st.set s v).set r u := by
  ext i <;> simp only [set, Function.update_apply]
  split_ifs <;> simp_all

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

/-- The instruction doing nothing (cost `1`). -/
def HProg.skip : HProg R := .loop (fun _ => false) .rst

lemma skip_spec (st : HSt R) : HLe x w HProg.skip st st 1 := HLe.loopF rfl

/-- Append the digits `ds` (most significant first) to `r`: `r := 2 r + d` for each `d`. -/
def HProg.pushDigits (r : Fin R) : List Bool → HProg R
  | [] => HProg.skip
  | d :: ds => .seq (if d then .one r else .dbl r) (HProg.pushDigits r ds)

/-- The value of a digit list, most significant first, appended to `v`. -/
def digitsVal (v : ℕ) : List Bool → ℕ
  | [] => v
  | d :: ds => digitsVal (2 * v + d.toNat) ds

lemma le_digitsVal (v : ℕ) : ∀ ds : List Bool, v ≤ digitsVal v ds
  | [] => le_rfl
  | d :: ds => le_trans (by omega) (le_digitsVal (2 * v + d.toNat) ds)

lemma digitsVal_append_singleton (d : Bool) : ∀ (v : ℕ) (ds : List Bool),
    digitsVal v (ds ++ [d]) = 2 * digitsVal v ds + d.toNat
  | v, [] => rfl
  | v, e :: ds => digitsVal_append_singleton d (2 * v + e.toNat) ds

lemma digitsVal_reverse (v : ℕ) : ∀ l : List Bool,
    digitsVal v l.reverse = v * 2 ^ l.length + Machines.valBits l
  | [] => by simp [digitsVal, Machines.valBits]
  | d :: l => by
    rw [List.reverse_cons, digitsVal_append_singleton, digitsVal_reverse v l]
    simp [Machines.valBits, pow_succ]; ring

lemma pushDigits_spec {r : Fin R} : ∀ (ds : List Bool) (st : HSt R),
    digitsVal (st.env r) ds < 2 ^ w →
    HLe x w (HProg.pushDigits r ds) st (st.set r (digitsVal (st.env r) ds))
      (ds.length * unitCost w + 1)
  | [], st, _ => (skip_spec st).of_eq (by simp [digitsVal]) (by simp)
  | d :: ds, st, h => by
    have h' : digitsVal (2 * st.env r + d.toNat) ds < 2 ^ w := h
    have hle := le_digitsVal (2 * st.env r + d.toNat) ds
    have h1 : HLe x w (if d then .one r else .dbl r) st (st.set r (2 * st.env r + d.toNat))
        (unitCost w) := by
      cases d
      · exact (HLe.of_runs (HRuns.dbl (by simp at hle h'; omega))).of_eq (by simp) le_rfl
      · exact (HLe.of_runs (HRuns.one (by simp at hle h'; omega))).of_eq (by simp) le_rfl
    have h2 := pushDigits_spec ds (st.set r (2 * st.env r + d.toNat))
      (by rw [HSt.set_env_self]; exact h')
    refine (h1.seq h2).of_eq (by simp [digitsVal]) (by simp; ring_nf; omega)

/-- `r := c`. -/
def HProg.setC (r : Fin R) (c : ℕ) : HProg R :=
  .seq (.clr r) (HProg.pushDigits r (Nat.bits c).reverse)

lemma setC_spec {r : Fin R} {c : ℕ} (hc : c < 2 ^ w) {st : HSt R} (hr : st.env r < 2 ^ w) :
    HLe x w (HProg.setC r c) st (st.set r c) ((Nat.bits c).length * unitCost w + unitCost w + 1) := by
  have e : digitsVal 0 (Nat.bits c).reverse = c := by
    rw [digitsVal_reverse, Machines.valBits_bits]; simp
  have h2 := pushDigits_spec (x := x) (r := r) (Nat.bits c).reverse (st.set r 0)
    (by simpa [e] using hc)
  refine ((HLe.of_runs (HRuns.clr hr)).seq h2).of_eq (by simp [e]) (by simp; omega)

/-! ## Counting loops -/

/-- `for i ∈ [0, lim): body`, with the flag `f` (`[i < lim]`) and the scratch register `t`. -/
def HProg.forUp (i lim f t : Fin R) (body : HProg R) : HProg R :=
  .seq (.clr i) (.seq (.lt f i lim)
    (.loop (fun v => (v f).isSome) (.seq body (.seq (HProg.inc i t) (.lt f i lim)))))

/-- The flag value `[a < b]`. -/
def ltFlag (a b : ℕ) : ℕ := if a < b then 1 else 0

/-- **Counting loops.** `S k` is the state at the start of iteration `k` (with `i = k` and the
flag set), `B k` the state after the body. -/
lemma forUp_spec {i lim f t : Fin R} {body : HProg R} (hil : i ≠ lim) (hif : i ≠ f)
    (hit : i ≠ t) (hlf : lim ≠ f) (hlt : lim ≠ t) (hft : f ≠ t) (L : ℕ) (hL : L + 1 < 2 ^ w)
    (st₀ : HSt R) (hi₀ : st₀.env i < 2 ^ w) (hf₀ : st₀.env f < 2 ^ w)
    (hl₀ : st₀.env lim = L)
    (S B : ℕ → HSt R) (T : ℕ)
    (hS0 : S 0 = (st₀.set i 0).set f (ltFlag 0 L))
    (hbody : ∀ k < L, HLe x w body (S k) (B k) T)
    (hB : ∀ k < L, (B k).env i = k ∧ (B k).env lim = L ∧ (B k).env f < 2 ^ w ∧
      (B k).env t < 2 ^ w)
    (hS : ∀ k < L, S (k + 1) = (((B k).set t 1).set i (k + 1)).set f (ltFlag (k + 1) L)) :
    HLe x w (HProg.forUp i lim f t body) st₀ (S L)
      (L * (T + 4 * unitCost w + 1) + 2 * unitCost w + 1) := by
  have h2 : (1 : ℕ) < 2 ^ w := by omega
  have hc1 : HLe x w (.clr i) st₀ (st₀.set i 0) (unitCost w) := HLe.of_runs (HRuns.clr hi₀)
  have hc2 : HLe x w (.lt f i lim) (st₀.set i 0) (S 0) (unitCost w) := by
    refine (HLe.of_runs (HRuns.lt hif.symm hlf.symm hil (by simp [HSt.set_env_ne _ hif.symm]; omega)
      (by simp) (by simp [HSt.set_env_ne _ hil.symm]; omega))).of_eq ?_ le_rfl
    rw [hS0]; simp [HSt.set_env_ne _ hil.symm, hl₀, ltFlag]
  have hview : ∀ k ≤ L, ((S k).view f).isSome = decide (k < L) := by
    intro k hk
    have : (S k).env f = ltFlag k L := by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [hS0]; simp
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [hS j (by omega)]; simp
    rw [HSt.view]
    unfold ltFlag at this
    split_ifs at this with h1 <;> simp [this, h1]
  have hloop := HLe.loop_seq_const (p := .seq body (.seq (HProg.inc i t) (.lt f i lim)))
    (c := fun v => (v f).isSome) L S (T + 4 * unitCost w) (fun k hk => by
      simpa [hk] using hview k hk.le) (by simpa using hview L le_rfl) (fun k hk => by
      obtain ⟨hBi, hBl, hBf, hBt⟩ := hB k hk
      have hinc := inc_spec (x := x) hit (st := B k) hBt (by omega)
      have hlt' : HLe x w (.lt f i lim) (((B k).set t 1).set i ((B k).env i + 1)) (S (k + 1))
          (unitCost w) := by
        refine (HLe.of_runs (HRuns.lt hif.symm hlf.symm hil ?_ ?_ ?_)).of_eq ?_ le_rfl
        · simp [HSt.set_env_ne _ hif.symm, HSt.set_env_ne _ hft]; omega
        · simp; omega
        · simp [HSt.set_env_ne _ hil.symm, HSt.set_env_ne _ hlt]; omega
        · rw [hS k hk, hBi]
          simp [HSt.set_env_ne _ hil.symm, HSt.set_env_ne _ hlt, hBl, ltFlag]
      exact ((hbody k hk).seq (hinc.seq hlt')).mono (by omega))
  refine (hc1.seq (hc2.seq hloop)).mono ?_
  nlinarith

end Lax119563Proofs.Reduction
