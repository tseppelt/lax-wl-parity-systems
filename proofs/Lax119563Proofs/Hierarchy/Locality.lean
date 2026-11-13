import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Lax119563Proofs.Hierarchy.Glue
import Lax119563Proofs.Hierarchy.Chain

/-!
# The linear case

The language of words whose last bit is `true` is decidable in linear time, but not in time
`O(n^a)` for `a < 1`: in fewer than `n - 1` steps a machine never scans the last input cell.
-/

open Lax489179.TuringMachine Lax119563.DeterministicTime Filter Topology

namespace Lax119563Proofs.Hierarchy

/-! ## Locality -/

/-- Two configurations that agree except possibly on cell `p` of tape `0`, with the head of
tape `0` at most `i`. -/
def CloseAt (M : Machine) (p : ℤ) (i : ℕ) (c c' : Config M) : Prop :=
  c.state = c'.state ∧ c.head = c'.head ∧ c.answer = c'.answer ∧
    (∀ j z, ¬ (j = 0 ∧ z = p) → c.tape j z = c'.tape j z) ∧ c.head 0 ≤ i

lemma CloseAt.step {M : Machine} {p : ℤ} {i : ℕ} {c c' : Config M} (h : CloseAt M p i c c')
    (hi : (i : ℤ) < p) : CloseAt M p (i + 1) (step M false c) (step M false c') := by
  obtain ⟨hs, hh, ha, ht, h0⟩ := h
  have hread : (fun j => c.tape j (c.head j)) = fun j => c'.tape j (c'.head j) := by
    funext j
    rw [← hh]
    apply ht
    rintro ⟨rfl, hz⟩
    omega
  unfold Lax489179.TuringMachine.step
  rw [← ha, ← hs, ← hread]
  rcases hca : c.answer with _ | b
  · dsimp only
    rcases M.transition c.state (fun j => c.tape j (c.head j)) false with b | ⟨q, w, mv⟩
    · exact ⟨rfl, hh, rfl, ht, by simp; omega⟩
    · refine ⟨rfl, by rw [hh], rfl, ?_, ?_⟩
      · intro j z hjz
        simp only
        rw [← hh]
        split_ifs
        · rfl
        · exact ht j z hjz
      · simp only
        rcases mv 0 <;> simp [Move.offset] <;> omega
  · dsimp only
    exact ⟨hs, hh, ha, ht, by omega⟩

lemma closeAt_drun {M : Machine} {p : ℤ} :
    ∀ (t i : ℕ) (c c' : Config M), CloseAt M p i c c' → (i + t : ℤ) ≤ p →
      (drun M t c).answer = (drun M t c').answer
  | 0, _, _, _, h, _ => h.2.2.1
  | t + 1, i, c, c', h, hp => by
    rw [drun_succ, drun_succ]
    exact closeAt_drun t (i + 1) _ _ (h.step (by omega)) (by push_cast; omega)

/-! ## The language and its decision -/

/-- Words whose last bit is `true`. -/
def lastTrue : Set (List Bool) := {x | x.getLast? = some true}

/-- Remember the last symbol of stack `0` on stack `1` while emptying stack `0`. -/
def lastProg (m : ℕ) : Prog 2 m :=
  .loop (fun r => (r 0).isSome)
    (.seq (.pop 1) (.seq (.ite (fun r => r 0 == some 1) (.push 1 1) (.push 1 0)) (.pop 0)))

lemma lastProg_runs (m : ℕ) :
    ∀ (l : List (Fin (m + 2))) (s : Stacks 2 m), s 0 = l →
      ∃ s', (lastProg m).Runs s s' (6 * l.length + 1) ∧
        tops s' 1 = match l.getLast? with
          | some a => some (if a = 1 then 1 else 0)
          | none => tops s 1
  | [], s, hs => ⟨s, .loopF (by simp [tops, hs]), by simp⟩
  | a :: l, s, hs => by
    set s₁ := Function.update s 1 (s 1).tail
    set b : Fin (m + 2) := if a = 1 then 1 else 0
    set s₂ := Function.update s₁ 1 (b :: s₁ 1)
    set s₃ := Function.update s₂ 0 (s₂ 0).tail
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    have hs₁0 : s₁ 0 = a :: l := by simp [s₁, Function.update_of_ne h01, hs]
    have hs₂0 : s₂ 0 = a :: l := by simp [s₂, Function.update_of_ne h01, hs₁0]
    have hs₃0 : s₃ 0 = l := by simp [s₃, hs₂0]
    have hs₃1 : s₃ 1 = b :: (s 1).tail := by
      simp [s₃, s₂, s₁, Function.update_of_ne h01.symm]
    have hbody : (Prog.seq (.pop 1) (.seq (.ite (fun r => r 0 == some 1) (.push 1 1) (.push 1 0))
        (.pop 0))).Runs s s₃ 5 := by
      refine .seq (t₁ := 1) (t₂ := 4) .pop (.seq (t₁ := 3) (t₂ := 1) ?_ .pop)
      by_cases ha : a = 1
      · have : b = 1 := by simp [b, ha]
        rw [show s₂ = Function.update s₁ 1 (1 :: s₁ 1) by rw [← this]]
        exact .iteT (by simp [tops, hs₁0, hs, ha]) .push
      · have : b = 0 := by simp [b, ha]
        rw [show s₂ = Function.update s₁ 1 (0 :: s₁ 1) by rw [← this]]
        exact .iteF (by simp [tops, hs₁0, hs, ha]) .push
    obtain ⟨s', hr, htop⟩ := lastProg_runs m l s₃ hs₃0
    refine ⟨s', ?_, ?_⟩
    · have := Prog.Runs.loopT
        (by simp [tops, hs] : (fun r : Fin 2 → Option (Fin (m + 2)) => (r 0).isSome) (tops s) = true)
        hbody hr
      rw [show 6 * (a :: l).length + 1 = 5 + (6 * l.length + 1) + 1 by
        rw [List.length_cons]; ring]
      exact this
    · rw [htop]
      cases l with
      | nil => simp [tops, hs₃1, b]
      | cons a' l' => simp only [List.getLast?_cons_cons, List.getLast?_cons, Option.getD_some]

/-- `lastTrue` is decidable in linear time. -/
lemma lastTrue_dt : DT lastTrue 1 := by
  let P := lastProg 0
  let ans : (Fin 2 → Option (Fin 2)) → Bool := fun r => r 1 == some 1
  refine ⟨P.toMachine ans, Prog.toMachine_deterministic _ _, 6, fun x => ?_⟩
  obtain ⟨s', hr, htop⟩ := lastProg_runs 0 (x.map (bitSym 0)) (inputStacks 1 0 x) rfl
  have hans := Prog.toMachine_answer (ans := ans) hr
  refine decidesWithin_mono ⟨_, hans, ?_⟩ ?_
  · simp only [ans, htop, lastTrue, Set.mem_setOf_eq, List.getLast?_map]
    rcases x.getLast? with _ | _ | _
    · simp [tops, inputStacks]
    · simp [bitSym]
    · simp [bitSym]
  · apply Nat.le_floor
    simp only [List.length_map, Real.rpow_one]
    push_cast
    linarith

/-- For `a < 1`, a machine running in time `C n^a + C` misses the last cell of long inputs. -/
lemma exists_len (C : ℕ) {a : ℝ} (ha : a < 1) :
    ∃ n : ℕ, 1 ≤ n ∧ (C : ℝ) * (n : ℝ) ^ a + C ≤ n - 1 := by
  have hy : 0 < 1 - a := by linarith
  have hpos : (0 : ℝ) < 1 / (2 * C + 2) := by positivity
  have e1 : ∀ᶠ x : ℝ in atTop, x ^ (-(1 - a)) < 1 / (2 * C + 2) :=
    (tendsto_order.1 (tendsto_rpow_neg_atTop hy)).2 _ hpos
  have e2 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually e1
  have e3 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (2 * C + 2 : ℝ))
  obtain ⟨n, h1, h2, h3⟩ := (e2.and (e3.and (eventually_ge_atTop 1))).exists
  refine ⟨n, h3, ?_⟩
  have hn : (0 : ℝ) < n := by exact_mod_cast h3
  have hsplit : (n : ℝ) ^ a = n * (n : ℝ) ^ (-(1 - a)) := by
    conv_lhs => rw [show a = 1 + -(1 - a) by ring]
    rw [Real.rpow_add hn, Real.rpow_one]
  rw [hsplit]
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have h4 : (C : ℝ) * (n * (n : ℝ) ^ (-(1 - a))) ≤ n / 2 := by
    have h5 : (n : ℝ) ^ (-(1 - a)) * (2 * C + 2) ≤ 1 := by
      rw [lt_div_iff₀ (by positivity)] at h1; linarith
    have h6 : 0 ≤ (n : ℝ) ^ (-(1 - a)) := Real.rpow_nonneg hn.le _
    nlinarith
  linarith

lemma lastTrue_not_dt {a : ℝ} (ha : a < 1) : ¬ DT lastTrue a := by
  rintro ⟨M, -, C, hC⟩
  obtain ⟨n, hn1, hn⟩ := exists_len C ha
  set x₀ := List.replicate (n - 1) false ++ [false]
  set x₁ := List.replicate (n - 1) false ++ [true]
  have hl₀ : x₀.length = n := by simp [x₀]; omega
  have hl₁ : x₁.length = n := by simp [x₁]; omega
  have ht : ⌊(C : ℝ) * (n : ℝ) ^ a + C⌋₊ ≤ n - 1 := by
    apply Nat.floor_le_of_le
    push_cast [hn1]
    linarith
  obtain ⟨b₀, hb₀, hP₀⟩ := hC x₀
  obtain ⟨b₁, hb₁, hP₁⟩ := hC x₁
  rw [hl₀] at hb₀
  rw [hl₁] at hb₁
  have hclose : CloseAt M ((n - 1 : ℕ) : ℤ) 0 (init M x₀) (init M x₁) := by
    refine ⟨rfl, rfl, rfl, ?_, by simp [init]⟩
    intro j z hjz
    simp only [init]
    by_cases hj : j = 0
    · subst hj
      by_cases hz : 0 ≤ z
      · simp only [true_and, hz, if_true]
        have hz' : z.toNat ≠ n - 1 := by
          intro h; apply hjz; refine ⟨rfl, ?_⟩; omega
        simp only [x₀, x₁]
        rcases lt_or_gt_of_ne hz' with h | h
        · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
        · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
      · simp [hz]
    · simp [hj]
  have heq := closeAt_drun _ 0 _ _ hclose (show ((0 : ℕ) : ℤ) + _ ≤ _ by exact_mod_cast
    (by omega : 0 + ⌊(C : ℝ) * (n : ℝ) ^ a + C⌋₊ ≤ n - 1))
  rw [← runOn_eq_drun, ← runOn_eq_drun] at heq
  beta_reduce at hb₀ hb₁
  rw [hb₀, hb₁] at heq
  cases heq
  have h0 : x₀ ∉ lastTrue := by simp [x₀, lastTrue]
  have h1 : x₁ ∈ lastTrue := by simp [x₁, lastTrue]
  exact h0 (hP₀.mp (hP₁.mpr h1))

theorem lin (a : ℝ) (ha : a < 1) : ∃ L, DT L 1 ∧ ¬ DT L a :=
  ⟨lastTrue, lastTrue_dt, lastTrue_not_dt ha⟩

end Lax119563Proofs.Hierarchy
