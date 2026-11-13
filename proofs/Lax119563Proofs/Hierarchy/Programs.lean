import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lax119563Proofs.Hierarchy.Stack

/-!
# A small library of stack programs

Specifications are exact descriptions of the final stacks (as `Function.update`s of the initial
ones) together with upper bounds on the cost (`Prog.RunsLe`).  Unary numbers are stacks
`List.replicate n 0`.
-/

open Function

namespace Lax119563Proofs.Hierarchy

variable {K m : ℕ}

namespace Prog

/-- `p` runs from `s` to `s'` within cost `T`. -/
def RunsLe (p : Prog K m) (s s' : Stacks K m) (T : ℕ) : Prop := ∃ t ≤ T, p.Runs s s' t

lemma Runs.le {p : Prog K m} {s s' : Stacks K m} {t : ℕ} (h : p.Runs s s' t) :
    p.RunsLe s s' t := ⟨t, le_rfl, h⟩

lemma RunsLe.mono {p : Prog K m} {s s' : Stacks K m} {T T' : ℕ} (h : p.RunsLe s s' T)
    (hT : T ≤ T') : p.RunsLe s s' T' := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t, by omega, h⟩

lemma RunsLe.seq {p q : Prog K m} {s₁ s₂ s₃ : Stacks K m} {T₁ T₂ : ℕ} (h₁ : p.RunsLe s₁ s₂ T₁)
    (h₂ : q.RunsLe s₂ s₃ T₂) : (seq p q).RunsLe s₁ s₃ (T₁ + T₂) := by
  obtain ⟨t₁, ht₁, h₁⟩ := h₁; obtain ⟨t₂, ht₂, h₂⟩ := h₂
  exact ⟨t₁ + t₂, by omega, .seq h₁ h₂⟩

lemma RunsLe.iteT {c} {p q : Prog K m} {s s' : Stacks K m} {T : ℕ} (hc : c (tops s) = true)
    (h : p.RunsLe s s' T) : (ite c p q).RunsLe s s' (T + 1) := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t + 1, by omega, .iteT hc h⟩

lemma RunsLe.iteF {c} {p q : Prog K m} {s s' : Stacks K m} {T : ℕ} (hc : c (tops s) = false)
    (h : q.RunsLe s s' T) : (ite c p q).RunsLe s s' (T + 1) := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t + 1, by omega, .iteF hc h⟩

lemma RunsLe.loopF {c} {p : Prog K m} {s : Stacks K m} (hc : c (tops s) = false) :
    (loop c p).RunsLe s s 1 := (Runs.loopF hc).le

lemma RunsLe.loopT {c} {p : Prog K m} {s₁ s₂ s₃ : Stacks K m} {T₁ T₂ : ℕ}
    (hc : c (tops s₁) = true) (h₁ : p.RunsLe s₁ s₂ T₁) (h₂ : (loop c p).RunsLe s₂ s₃ T₂) :
    (loop c p).RunsLe s₁ s₃ (T₁ + T₂ + 1) := by
  obtain ⟨t₁, ht₁, h₁⟩ := h₁; obtain ⟨t₂, ht₂, h₂⟩ := h₂
  exact ⟨t₁ + t₂ + 1, by omega, .loopT hc h₁ h₂⟩

lemma RunsLe.skip (s : Stacks K m) : (skip : Prog K m).RunsLe s s 1 := Runs.skip.le

lemma RunsLe.push (i : Fin K) (a : Fin (m + 2)) (s : Stacks K m) :
    (push i a).RunsLe s (update s i (a :: s i)) 2 := Runs.push.le

lemma RunsLe.pop (i : Fin K) (s : Stacks K m) :
    (pop i).RunsLe s (update s i (s i).tail) 1 := Runs.pop.le

lemma RunsLe.of_eq {p : Prog K m} {s s₁ s₂ : Stacks K m} {T T' : ℕ} (h : p.RunsLe s s₁ T)
    (hs : s₁ = s₂) (hT : T ≤ T') : p.RunsLe s s₂ T' := hs ▸ h.mono hT

/-- Prove an equality of stacks given by `Function.update`s pointwise. -/
macro "stacks_eq" : tactic =>
  `(tactic| (funext k; simp only [Function.update_apply]; split_ifs <;> simp_all))

/-- Repeat a program `n` times. -/
def rep (p : Prog K m) : ℕ → Prog K m
  | 0 => skip
  | n + 1 => seq p (rep p n)

/-! ## Moving symbols -/

/-- Push onto `j` the top symbol of `i`, provided it occurs in `as`. -/
def pushTopOf (i j : Fin K) : List (Fin (m + 2)) → Prog K m
  | [] => skip
  | a :: as => ite (fun r => r i == some a) (push j a) (pushTopOf i j as)

lemma pushTopOf_runs (i j : Fin K) {s : Stacks K m} {a : Fin (m + 2)}
    (ha : tops s i = some a) :
    ∀ as : List (Fin (m + 2)), a ∈ as →
      (pushTopOf i j as).RunsLe s (update s j (a :: s j)) (as.length + 2)
  | [], h => by simp at h
  | b :: as, h => by
    by_cases hb : b = a
    · subst hb
      exact ((RunsLe.push j b s).iteT (by simp [ha])).mono (by simp)
    · have : a ∈ as := by simp at h; tauto
      exact ((pushTopOf_runs i j ha as this).iteF (by simp [ha, Ne.symm hb])).mono (by simp)

/-- Move the top symbol of `i` onto `j`. -/
def moveOne (i j : Fin K) : Prog K m := seq (pushTopOf i j (List.finRange (m + 2))) (pop i)

lemma moveOne_runs {i j : Fin K} (hij : i ≠ j) {s : Stacks K m} {a : Fin (m + 2)}
    {l : List (Fin (m + 2))} (hs : s i = a :: l) :
    (moveOne i j).RunsLe s (update (update s i l) j (a :: s j)) (m + 5) := by
  have h1 := pushTopOf_runs i j (s := s) (by simp [tops, hs]) (List.finRange (m + 2))
    (List.mem_finRange a)
  have h2 := RunsLe.pop i (update s j (a :: s j))
  exact (h1.seq h2).of_eq (by stacks_eq) (by simp)

/-- Move all of `i` onto `j` (reversing it). -/
def moveAll (i j : Fin K) : Prog K m := loop (fun r => (r i).isSome) (moveOne i j)

lemma moveAll_runs {i j : Fin K} (hij : i ≠ j) :
    ∀ (l : List (Fin (m + 2))) (s : Stacks K m), s i = l →
      (moveAll i j).RunsLe s (update (update s i []) j (l.reverse ++ s j))
        ((m + 6) * l.length + 1)
  | [], s, hs =>
    (RunsLe.loopF (p := moveOne i j) (c := fun r => (r i).isSome) (s := s)
      (by simp [tops, hs])).of_eq (by stacks_eq) (by simp)
  | a :: l, s, hs => by
    have h1 := moveOne_runs hij hs
    have h2 := moveAll_runs hij l (update (update s i l) j (a :: s j))
      (by simp [update_of_ne hij])
    exact (RunsLe.loopT (c := fun r => (r i).isSome) (by simp [tops, hs]) h1 h2).of_eq
      (by stacks_eq) (le_of_eq (by simp only [List.length_cons]; ring))

/-! ## Unary numbers -/

/-- The unary number `n`. -/
abbrev unary (m n : ℕ) : List (Fin (m + 2)) := List.replicate n 0

/-- Empty stack `i`. -/
def clear (i : Fin K) : Prog K m := loop (fun r => (r i).isSome) (pop i)

lemma clear_runs (i : Fin K) :
    ∀ (l : List (Fin (m + 2))) (s : Stacks K m), s i = l →
      (clear i).RunsLe s (update s i []) (2 * l.length + 1)
  | [], s, hs =>
    (RunsLe.loopF (p := pop i) (c := fun r => (r i).isSome) (s := s)
      (by simp [tops, hs])).of_eq (by stacks_eq) (by simp)
  | a :: l, s, hs => by
    have h2 := clear_runs i l (update s i (s i).tail) (by simp [hs])
    exact (RunsLe.loopT (c := fun r => (r i).isSome) (by simp [tops, hs]) (RunsLe.pop i s)
      h2).of_eq (by stacks_eq) (le_of_eq (by simp only [List.length_cons]; ring))

/-- Move the unary number on `i` to `j` and `h` (adding it to both). -/
def splitTwo (i j h : Fin K) : Prog K m :=
  loop (fun r => (r i).isSome) (seq (pop i) (seq (push h 0) (push j 0)))

lemma splitTwo_runs {i j h : Fin K} (hij : i ≠ j) (hih : i ≠ h) (hjh : j ≠ h) :
    ∀ (n : ℕ) (s : Stacks K m), s i = unary m n →
      (splitTwo i j h).RunsLe s
        (update (update (update s i []) j (unary m n ++ s j)) h (unary m n ++ s h)) (6 * n + 1)
  | 0, s, hs =>
    (RunsLe.loopF (p := seq (pop i) (seq (push h 0) (push j 0)))
      (c := fun r => (r i).isSome) (s := s) (by simp [tops, hs])).of_eq (by stacks_eq) (by simp)
  | n + 1, s, hs => by
    set s₁ := update (update (update s i (unary m n)) h (0 :: s h)) j (0 :: s j)
    have hb : (seq (pop i) (seq (push h 0) (push j 0)) : Prog K m).RunsLe s s₁ 5 :=
      ((RunsLe.pop i s).seq ((RunsLe.push h 0 _).seq (RunsLe.push j 0 _))).of_eq
        (by simp only [s₁, hs, List.replicate_succ, List.tail_cons]; stacks_eq) (by simp)
    have h2 := splitTwo_runs hij hih hjh n s₁ (by simp [s₁, update_of_ne hij, update_of_ne hih])
    exact (RunsLe.loopT (c := fun r => (r i).isSome) (by simp [tops, hs]) hb h2).of_eq
      (by simp only [s₁, List.replicate_succ']; stacks_eq) (le_of_eq (by ring))

/-- Add the unary number on `i` to `j`, restoring `i` through the empty helper `h`. -/
def addTo (i j h : Fin K) : Prog K m := seq (splitTwo i j h) (moveAll h i)

lemma addTo_runs {i j h : Fin K} (hij : i ≠ j) (hih : i ≠ h) (hjh : j ≠ h) {n : ℕ}
    {s : Stacks K m} (hs : s i = unary m n) (hh : s h = []) :
    (addTo i j h).RunsLe s (update s j (unary m n ++ s j)) ((m + 12) * n + 2) := by
  have h1 := splitTwo_runs hij hih hjh n s hs
  have h2 := moveAll_runs hih.symm (unary m n)
    (update (update (update s i []) j (unary m n ++ s j)) h (unary m n ++ s h))
    (by simp [hh])
  exact (h1.seq h2).of_eq (by stacks_eq) (le_of_eq (by simp; ring))

/-- Pop the symbols `0` from the top of `i`, counting them in unary on `j`. -/
def popZeros (i j : Fin K) : Prog K m :=
  loop (fun r => r i == some 0) (seq (pop i) (push j 0))

lemma popZeros_runs {i j : Fin K} (hij : i ≠ j) (l : List (Fin (m + 2)))
    (hl : l.head? ≠ some 0) :
    ∀ (n : ℕ) (s : Stacks K m), s i = unary m n ++ l →
      (popZeros i j).RunsLe s (update (update s i l) j (unary m n ++ s j)) (4 * n + 1)
  | 0, s, hs =>
    (RunsLe.loopF (p := seq (pop i) (push j 0)) (c := fun r => r i == some 0) (s := s)
      (by simpa [tops, hs] using hl)).of_eq (by simp at hs; stacks_eq) (by simp)
  | n + 1, s, hs => by
    set s₁ := update (update s i (unary m n ++ l)) j (0 :: s j) with hs₁
    have h1 : (seq (pop i) (push j 0) : Prog K m).RunsLe s s₁ 3 :=
      ((RunsLe.pop i s).seq (RunsLe.push j 0 _)).of_eq
        (by simp only [hs₁, hs, List.replicate_succ, List.cons_append, List.tail_cons]; stacks_eq)
        le_rfl
    have h2 := popZeros_runs hij l hl n s₁ (by simp [s₁, update_of_ne hij])
    exact (RunsLe.loopT (c := fun r => r i == some 0) (by simp [tops, hs, List.replicate_succ])
      h1 h2).of_eq (by simp only [hs₁, List.replicate_succ', List.append_assoc,
        List.singleton_append]; stacks_eq) (le_of_eq (by ring))

/-- Move all of `i` onto `j` (reversing it), counting the symbols in unary on `c`. -/
def moveCount (i j c : Fin K) : Prog K m :=
  loop (fun r => (r i).isSome) (seq (moveOne i j) (push c 0))

lemma moveCount_runs {i j c : Fin K} (hij : i ≠ j) (hic : i ≠ c) (hjc : j ≠ c) :
    ∀ (l : List (Fin (m + 2))) (s : Stacks K m), s i = l →
      (moveCount i j c).RunsLe s
        (update (update (update s i []) j (l.reverse ++ s j)) c (unary m l.length ++ s c))
        ((m + 8) * l.length + 1)
  | [], s, hs =>
    (RunsLe.loopF (p := seq (moveOne i j) (push c 0)) (c := fun r => (r i).isSome) (s := s)
      (by simp [tops, hs])).of_eq (by stacks_eq) (by simp)
  | a :: l, s, hs => by
    set s₁ := update (update (update s i l) j (a :: s j)) c (0 :: s c) with hs₁
    have h1 : (seq (moveOne i j) (push c 0) : Prog K m).RunsLe s s₁ (m + 7) :=
      ((moveOne_runs hij hs).seq (RunsLe.push c 0 _)).of_eq (by stacks_eq) le_rfl
    have h2 := moveCount_runs hij hic hjc l s₁ (by simp [s₁, update_of_ne hij, update_of_ne hic])
    exact (RunsLe.loopT (c := fun r => (r i).isSome) (by simp [tops, hs]) h1 h2).of_eq
      (by simp only [hs₁, List.length_cons, List.replicate_succ', List.append_assoc,
        List.singleton_append, List.reverse_cons]; stacks_eq)
      (le_of_eq (by simp only [List.length_cons]; ring))

/-- Multiply the unary number on `p` by the one on `n` (helpers `q`, `h` empty). -/
def mulBy (p n q h : Fin K) : Prog K m :=
  seq (loop (fun r => (r p).isSome) (seq (pop p) (addTo n q h))) (moveAll q p)

lemma mulBy_loop_runs {p n q h : Fin K} (hpn : p ≠ n) (hpq : p ≠ q) (hph : p ≠ h) (hnq : n ≠ q)
    (hnh : n ≠ h) (hqh : q ≠ h) {b : ℕ} :
    ∀ (a : ℕ) (s : Stacks K m), s p = unary m a → s n = unary m b → s h = [] →
      (loop (fun r => (r p).isSome) (seq (pop p) (addTo n q h))).RunsLe s
        (update (update s p []) q (unary m (a * b) ++ s q)) (a * ((m + 12) * b + 4) + 1)
  | 0, s, hs, _, _ =>
    (RunsLe.loopF (p := seq (pop p) (addTo n q h)) (c := fun r => (r p).isSome) (s := s)
      (by simp [tops, hs])).of_eq (by simp at hs; stacks_eq) (by simp)
  | a + 1, s, hs, hn, hh => by
    set s₁ := update (update s p (unary m a)) q (unary m b ++ s q) with hs₁
    have h1 : (seq (pop p) (addTo n q h) : Prog K m).RunsLe s s₁ ((m + 12) * b + 3) :=
      ((RunsLe.pop p s).seq (addTo_runs (n := b) (s := update s p (s p).tail) hnq hnh hqh
        (by simp [update_of_ne hpn.symm, hn]) (by simp [update_of_ne hph.symm, hh]))).of_eq
        (by simp only [hs₁, hs, List.replicate_succ, List.tail_cons]; stacks_eq) (by omega)
    have h2 := mulBy_loop_runs (b := b) hpn hpq hph hnq hnh hqh a s₁
      (by simp [s₁, update_of_ne hpq])
      (by simp [s₁, update_of_ne hnq, update_of_ne hpn.symm, hn])
      (by simp [s₁, update_of_ne hqh.symm, update_of_ne hph.symm, hh])
    refine (RunsLe.loopT (c := fun r => (r p).isSome) (by simp [tops, hs, List.replicate_succ])
      h1 h2).of_eq ?_ (le_of_eq (by ring))
    have : unary m ((a + 1) * b) = unary m (a * b) ++ unary m b := by
      rw [List.replicate_append_replicate]; congr 1; ring
    rw [this, hs₁, List.append_assoc]
    stacks_eq

lemma mulBy_runs {p n q h : Fin K} (hpn : p ≠ n) (hpq : p ≠ q) (hph : p ≠ h) (hnq : n ≠ q)
    (hnh : n ≠ h) (hqh : q ≠ h) {a b : ℕ} {s : Stacks K m} (hs : s p = unary m a)
    (hn : s n = unary m b) (hq : s q = []) (hh : s h = []) :
    (mulBy p n q h).RunsLe s (update s p (unary m (a * b))) ((2 * m + 20) * (a + 1) * (b + 1)) := by
  have h1 := mulBy_loop_runs hpn hpq hph hnq hnh hqh a s hs hn hh
  have h2 := moveAll_runs hpq.symm (unary m (a * b))
    (update (update s p []) q (unary m (a * b) ++ s q)) (by simp [hq])
  refine (h1.seq h2).of_eq (by simp only [List.reverse_replicate]; stacks_eq) ?_
  simp only [List.length_replicate]
  nlinarith [Nat.zero_le (a * b), Nat.zero_le m, Nat.zero_le a, Nat.zero_le b]

lemma rep_seq_runs {p : Prog K m} {f : ℕ → Stacks K m} {c : ℕ → ℕ}
    (h : ∀ k, p.RunsLe (f k) (f (k + 1)) (c k)) :
    ∀ r k, (rep p r).RunsLe (f k) (f (k + r)) ((Finset.range r).sum (fun i => c (k + i)) + 1)
  | 0, k => (RunsLe.skip _).of_eq (by simp) (by simp)
  | r + 1, k => by
    have := (h k).seq (rep_seq_runs h r (k + 1))
    refine this.of_eq (by rw [show k + 1 + r = k + (r + 1) by omega]) (le_of_eq ?_)
    rw [Finset.sum_range_succ']
    simp only [add_zero]
    have : ∀ i, k + 1 + i = k + (i + 1) := fun i => by omega
    simp only [this]
    ring

/-- Compute on `p` (empty) the `r`-th power of the unary number on `n` (helpers `q`, `h`
empty). -/
def power (p n q h : Fin K) (r : ℕ) : Prog K m := seq (push p 0) (rep (mulBy p n q h) r)

lemma power_runs {p n q h : Fin K} (hpn : p ≠ n) (hpq : p ≠ q) (hph : p ≠ h) (hnq : n ≠ q)
    (hnh : n ≠ h) (hqh : q ≠ h) {b : ℕ} (r : ℕ) {s : Stacks K m} (hp : s p = [])
    (hn : s n = unary m b) (hq : s q = []) (hh : s h = []) :
    (power p n q h r).RunsLe s (update s p (unary m (b ^ r)))
      (r * ((4 * m + 40) * (b + 1) ^ r) + 3) := by
  set f : ℕ → Stacks K m := fun k => update s p (unary m (b ^ k))
  have hstep : ∀ k, (mulBy p n q h).RunsLe (f k) (f (k + 1))
      ((2 * m + 20) * (b ^ k + 1) * (b + 1)) := by
    intro k
    refine (mulBy_runs hpn hpq hph hnq hnh hqh (s := f k) (by simp [f])
      (by simp [f, update_of_ne hpn.symm, hn]) (by simp [f, update_of_ne hpq.symm, hq])
      (by simp [f, update_of_ne hph.symm, hh])).of_eq (by simp [f, pow_succ]) le_rfl
  have h2 := rep_seq_runs hstep r 0
  have h1 : (push p 0 : Prog K m).RunsLe s (f 0) 2 :=
    (RunsLe.push p 0 s).of_eq (by simp [f, hp]) le_rfl
  refine (h1.seq (h2.of_eq (s₂ := f r) (by simp) le_rfl)).of_eq rfl ?_
  · simp only [zero_add]
    have hb : ∀ i < r, (2 * m + 20) * (b ^ i + 1) * (b + 1) ≤ (4 * m + 40) * (b + 1) ^ r := by
      intro i hi
      have h3 : b ^ i + 1 ≤ 2 * (b + 1) ^ i := by
        have := Nat.pow_le_pow_left (show b ≤ b + 1 by omega) i
        have := Nat.one_le_pow i (b + 1) (Nat.succ_pos b)
        omega
      have h4 : (b + 1) ^ i * (b + 1) ≤ (b + 1) ^ r := by
        rw [← pow_succ]; exact Nat.pow_le_pow_right (Nat.succ_pos b) hi
      calc (2 * m + 20) * (b ^ i + 1) * (b + 1) ≤ (2 * m + 20) * (2 * (b + 1) ^ i) * (b + 1) := by
            gcongr
        _ = (4 * m + 40) * ((b + 1) ^ i * (b + 1)) := by ring
        _ ≤ (4 * m + 40) * (b + 1) ^ r := by gcongr
    have := Finset.sum_le_sum (fun i hi => hb i (Finset.mem_range.mp hi))
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
    omega

end Prog

end Lax119563Proofs.Hierarchy
