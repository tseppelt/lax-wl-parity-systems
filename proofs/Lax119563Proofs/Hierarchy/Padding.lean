import Lax119563Proofs.Hierarchy.Programs
import Lax119563Proofs.Hierarchy.Glue
import Lax119563Proofs.Hierarchy.Chain

/-!
# Padding

For a machine `ML` and constants `C s`, the padded language
`padLang ML C s = {x ++ [true] ++ 0^j | ML accepts x within ((C + 1) (j + 1))^s steps}`
is decidable in time `O(n^s)` by a clocked run of `ML` (`padLang_dt`).  Conversely, if
`ML` decides `L` within `C n^{s r} + C` steps and `padLang ML C s ∈ DTIME(n^a)` with `a ≥ 1`,
then `L ∈ DTIME(n^{a r})`: write `0^{|x|^r}` behind `x ++ [true]` and run the decider of the
padded language (`dt_of_padLang`).
-/

open Lax489179.TuringMachine Lax119563.DeterministicTime Function

namespace Lax119563Proofs.Hierarchy

open Prog

lemma update_far {α : Type} {N : ℕ} {f : Fin N → α} {i j : Fin N} {v : α} (h : i.val ≠ j.val) :
    update f j v i = f i := update_of_ne (Fin.ne_of_val_ne h) _ _

/-! ## Words with a last `true` -/

lemma split_last_true (y : List Bool) :
    (∃ x j, y = x ++ true :: List.replicate j false) ∨ ∃ n, y = List.replicate n false := by
  induction y using List.reverseRecOn with
  | nil => exact .inr ⟨0, rfl⟩
  | append_singleton y b ih =>
    cases b
    · rcases ih with ⟨x, j, rfl⟩ | ⟨n, rfl⟩
      · exact .inl ⟨x, j + 1, by simp [List.replicate_succ']⟩
      · exact .inr ⟨n + 1, by simp [List.replicate_succ']⟩
    · exact .inl ⟨y, 0, rfl⟩

lemma replicate_true_cancel :
    ∀ (j j' : ℕ) (l l' : List Bool),
      List.replicate j false ++ true :: l = List.replicate j' false ++ true :: l' → j = j' ∧ l = l'
  | 0, 0, l, l', h => by simpa using h
  | 0, j' + 1, l, l', h => by simp [List.replicate_succ] at h
  | j + 1, 0, l, l', h => by simp [List.replicate_succ] at h
  | j + 1, j' + 1, l, l', h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨h1, h2⟩ := replicate_true_cancel j j' l l' h
    exact ⟨by omega, h2⟩

lemma last_true_unique {x x' : List Bool} {j j' : ℕ}
    (h : x ++ true :: List.replicate j false = x' ++ true :: List.replicate j' false) :
    x = x' ∧ j = j' := by
  have := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate, List.append_assoc,
    List.singleton_append] at this
  obtain ⟨h1, h2⟩ := replicate_true_cancel j j' _ _ this
  exact ⟨by simpa using h2, h1⟩

/-! ## The padded language and its decider -/

section Decider

variable (ML : Machine) (C s : ℕ)

/-- The padded language. -/
def padLang : Set (List Bool) :=
  {y | ∃ x j, y = x ++ true :: List.replicate j false ∧
    (runOn ML x (((C + 1) * (j + 1)) ^ s)).answer = some true}

/-- Stack indices of the decider: scratch stacks after the clock. -/
def d1 (k : ℕ) (hk : k < 5 := by omega) : Fin (ML.tapes + 1 + 5 + 1) := ⟨ML.tapes + 2 + k, by omega⟩

/-- The preparation of the decider of `padLang`. -/
def padPrep : Prog (ML.tapes + 1 + 5 + 1) ML.symbols :=
  seq (moveAll 0 (d1 ML 0))
    (seq (popZeros (d1 ML 0) (d1 ML 1))
      (ite (fun r => r (d1 ML 0) == some 1)
        (seq (pop (d1 ML 0))
          (seq (moveAll (d1 ML 0) 0)
            (seq (push (d1 ML 1) 0)
              (seq (rep (addTo (d1 ML 1) (d1 ML 2) (d1 ML 3)) (C + 1))
                (power (clockIdx ML 5) (d1 ML 2) (d1 ML 4) (d1 ML 3) s)))))
        skip))

/-- The decider of `padLang`. -/
noncomputable def padDecider : Machine := thenClocked ML 5 (padPrep ML C s)

end Decider

section Spec

variable {ML : Machine} {C s : ℕ}

lemma map_bitSym_pad (m : ℕ) (x : List Bool) (j : ℕ) :
    ((x ++ true :: List.replicate j false).map (bitSym m)).reverse =
      unary m j ++ (1 :: (x.map (bitSym m)).reverse) := by
  simp [List.reverse_append, List.map_replicate, bitSym, List.reverse_replicate]

/-- The cost bound of `padPrep` when the input has a last `true`. -/
def padCost (m n j xl C s : ℕ) : ℕ :=
  (m + 6) * n + 1 + (4 * j + 1 + (1 + ((m + 6) * xl + 1 + (2 +
    ((Finset.range (C + 1)).sum (fun _ => (m + 12) * (j + 1) + 2) + 1 +
      (s * ((4 * m + 40) * ((C + 1) * (j + 1) + 1) ^ s) + 3)))) + 1))

/-- Stacks of the decider in the shape used by `padPrep`. -/
def pst (ML : Machine) (a0 aA aJ aB aK : List (Fin (ML.symbols + 2))) :
    Stacks (ML.tapes + 1 + 5 + 1) ML.symbols := fun i =>
  if i.val = 0 then a0 else if i.val = ML.tapes + 2 then aA else
  if i.val = ML.tapes + 3 then aJ else if i.val = ML.tapes + 4 then aB else
  if i.val = ML.tapes + 1 then aK else []

/-- Prove equalities between `pst` stacks and their updates. -/
macro "pst_eq" : tactic =>
  `(tactic| (funext i; simp only [pst, Function.update_apply, Fin.ext_iff, Fin.val_zero, d1,
    clockIdx]; split_ifs <;> first | omega | rfl | simp_all))

lemma padPrep_runs_true (x : List Bool) (j : ℕ) :
    ∃ s', (padPrep ML C s).RunsLe (inputStacks _ _ (x ++ true :: List.replicate j false)) s'
        (padCost ML.symbols (x ++ true :: List.replicate j false).length j x.length C s) ∧
      HandsOver ML s' x ∧ (s' (clockIdx ML 5)).length = ((C + 1) * (j + 1)) ^ s := by
  have ne : ∀ a b : Fin (ML.tapes + 1 + 5 + 1), a.val ≠ b.val → a ≠ b :=
    fun a b h => Fin.ne_of_val_ne h
  have v0 : (0 : Fin (ML.tapes + 1 + 5 + 1)).val = 0 := rfl
  set m := ML.symbols
  set y := x ++ true :: List.replicate j false
  have hs0 : inputStacks (ML.tapes + 1 + 5) m y = pst ML (y.map (bitSym m)) [] [] [] [] := by
    funext i
    simp only [inputStacks, pst, Fin.ext_iff, Fin.val_zero]
    split_ifs <;> first | omega | rfl
  rw [hs0]
  -- 1. reverse the input onto `A`
  have h1 : (moveAll 0 (d1 ML 0) : Prog _ m).RunsLe (pst ML (y.map (bitSym m)) [] [] [] [])
      (pst ML [] (unary m j ++ (1 :: (x.map (bitSym m)).reverse)) [] [] []) ((m + 6) * y.length + 1) :=
    (moveAll_runs (ne _ _ (by simp [d1])) (y.map (bitSym m)) _ (by simp [pst])).of_eq
      (by rw [map_bitSym_pad]; pst_eq) (by simp)
  -- 2. count the trailing `false`s on `J`
  have h2 : (popZeros (d1 ML 0) (d1 ML 1) : Prog _ m).RunsLe
      (pst ML [] (unary m j ++ (1 :: (x.map (bitSym m)).reverse)) [] [] [])
      (pst ML [] (1 :: (x.map (bitSym m)).reverse) (unary m j) [] []) (4 * j + 1) :=
    (popZeros_runs (ne _ _ (by simp [d1])) (1 :: (x.map (bitSym m)).reverse) (by simp) j _
      (by simp [pst, d1])).of_eq (by pst_eq) le_rfl
  -- 3. the branch on the `true`
  have h3 : (pop (d1 ML 0) : Prog _ m).RunsLe (pst ML [] (1 :: (x.map (bitSym m)).reverse) (unary m j) [] [])
      (pst ML [] (x.map (bitSym m)).reverse (unary m j) [] []) 1 :=
    (RunsLe.pop _ _).of_eq (by pst_eq) le_rfl
  have h4 : (moveAll (d1 ML 0) 0 : Prog _ m).RunsLe (pst ML [] (x.map (bitSym m)).reverse (unary m j) [] [])
      (pst ML (x.map (bitSym m)) [] (unary m j) [] []) ((m + 6) * x.length + 1) :=
    (moveAll_runs (ne _ _ (by simp [d1])) (x.map (bitSym m)).reverse _ (by simp [pst, d1])).of_eq
      (by pst_eq) (by simp)
  set f : ℕ → Stacks _ m := fun k => pst ML (x.map (bitSym m)) [] (unary m (j + 1)) (unary m (k * (j + 1))) []
  have h5 : (push (d1 ML 1) 0 : Prog _ m).RunsLe (pst ML (x.map (bitSym m)) [] (unary m j) [] []) (f 0) 2 :=
    (RunsLe.push _ _ _).of_eq (by simp only [f, List.replicate_succ]; pst_eq) le_rfl
  have hstep : ∀ k, (addTo (d1 ML 1) (d1 ML 2) (d1 ML 3) : Prog _ m).RunsLe (f k) (f (k + 1))
      ((m + 12) * (j + 1) + 2) := by
    intro k
    refine (addTo_runs (n := j + 1) (ne _ _ (by simp [d1])) (ne _ _ (by simp [d1]))
      (ne _ _ (by simp [d1])) (by simp [f, pst, d1]) (by simp [f, pst, d1])).of_eq ?_ le_rfl
    have : unary m (j + 1) ++ unary m (k * (j + 1)) = unary m ((k + 1) * (j + 1)) := by
      rw [List.replicate_append_replicate]; congr 1; ring
    simp only [f]
    rw [show pst ML (x.map (bitSym m)) [] (unary m (j + 1)) (unary m (k * (j + 1))) [] (d1 ML 2) =
      unary m (k * (j + 1)) by simp [pst, d1], this]
    pst_eq
  have h6 := rep_seq_runs hstep (C + 1) 0
  simp only [zero_add] at h6
  set Bv := (C + 1) * (j + 1)
  have h7 := power_runs (p := clockIdx ML 5) (n := d1 ML 2) (q := d1 ML 4) (h := d1 ML 3) (b := Bv)
    (ne _ _ (by simp [d1, clockIdx])) (ne _ _ (by simp [d1, clockIdx]))
    (ne _ _ (by simp [d1, clockIdx])) (ne _ _ (by simp [d1])) (ne _ _ (by simp [d1]))
    (ne _ _ (by simp [d1])) s (s := f (C + 1))
    (by simp [f, pst, clockIdx]) (by simp [f, pst, d1, Bv]) (by simp [f, pst, d1])
    (by simp [f, pst, d1])
  have hc : (fun r : Fin (ML.tapes + 1 + 5 + 1) → Option (Fin (m + 2)) => r (d1 ML 0) == some 1)
      (tops (pst ML [] (1 :: (x.map (bitSym m)).reverse) (unary m j) [] [])) = true := by
    simp [tops, pst, d1]
  refine ⟨_, h1.seq (h2.seq (RunsLe.iteT hc (h3.seq (h4.seq (h5.seq (h6.seq h7)))))), ?_, ?_⟩
  · intro i
    refine ⟨fun hi => ?_, fun hi1 hi2 => ?_⟩
    · simp only [f, update_apply, Fin.ext_iff, clockIdx, pst]
      split_ifs <;> first | omega | rfl
    · simp only [f, update_apply, Fin.ext_iff, clockIdx, pst]
      split_ifs <;> first | omega | rfl
  · simp

lemma padPrep_runs_false (n : ℕ) :
    ∃ s', (padPrep ML C s).RunsLe (inputStacks _ _ (List.replicate n false)) s'
        ((ML.symbols + 6) * n + 1 + (4 * n + 1 + (1 + 1))) ∧
      HandsOver ML s' [] ∧ (s' (clockIdx ML 5)).length = 0 := by
  have ne : ∀ a b : Fin (ML.tapes + 1 + 5 + 1), a.val ≠ b.val → a ≠ b :=
    fun a b h => Fin.ne_of_val_ne h
  set m := ML.symbols
  have hs0 : inputStacks (ML.tapes + 1 + 5) m (List.replicate n false) =
      pst ML (unary m n) [] [] [] [] := by
    funext i
    simp only [inputStacks, pst, Fin.ext_iff, Fin.val_zero, List.map_replicate]
    split_ifs <;> first | omega | rfl | simp_all [bitSym]
  rw [hs0]
  have h1 : (moveAll 0 (d1 ML 0) : Prog _ m).RunsLe (pst ML (unary m n) [] [] [] [])
      (pst ML [] (unary m n ++ []) [] [] []) ((m + 6) * n + 1) :=
    (moveAll_runs (ne _ _ (by simp [d1])) (unary m n) _ (by simp [pst])).of_eq
      (by simp only [List.reverse_replicate]; pst_eq) (by simp)
  have h2 : (popZeros (d1 ML 0) (d1 ML 1) : Prog _ m).RunsLe
      (pst ML [] (unary m n ++ []) [] [] []) (pst ML [] [] (unary m n) [] []) (4 * n + 1) :=
    (popZeros_runs (ne _ _ (by simp [d1])) [] (by simp) n _ (by simp [pst, d1])).of_eq
      (by pst_eq) le_rfl
  have hc : (fun r : Fin (ML.tapes + 1 + 5 + 1) → Option (Fin (m + 2)) => r (d1 ML 0) == some 1)
      (tops (pst ML [] [] (unary m n) [] [])) = false := by
    simp [tops, pst, d1]
  refine ⟨_, h1.seq (h2.seq (RunsLe.iteF hc (RunsLe.skip _))), ?_, ?_⟩
  · intro i
    refine ⟨fun hi => ?_, fun hi1 hi2 => ?_⟩
    · simp only [pst]; split_ifs <;> first | omega | rfl
    · simp only [pst]; split_ifs <;> first | omega | rfl
  · simp [pst, clockIdx]

/-- The constant of the time bound of `padDecider`. -/
def padK (m C s : ℕ) : ℕ := 2 * m + 28 + (C + 1) * (m + 14) + (s + 1) * (4 * m + 40) * (C + 2) ^ s

lemma padCost_le {m n j xl C s : ℕ} (hs : 1 ≤ s) (hj : j ≤ n) (hxl : xl ≤ n) :
    padCost m n j xl C s + ((C + 1) * (j + 1)) ^ s + 1 ≤ padK m C s * (n + 1) ^ s := by
  set P := (n + 1) ^ s
  have hP : n + 1 ≤ P := Nat.le_self_pow (by omega) _
  have hQ : ((C + 1) * (j + 1) + 1) ^ s ≤ (C + 2) ^ s * P := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by nlinarith) s
  have hU : ((C + 1) * (j + 1)) ^ s ≤ (C + 2) ^ s * P :=
    le_trans (Nat.pow_le_pow_left (by omega) s) hQ
  unfold padCost padK
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h_a : (2 * m + 16) * (n + 1) ≤ (2 * m + 16) * P := Nat.mul_le_mul_left _ hP
  have h_b : (C + 1) * (m + 14) * (n + 1) ≤ (C + 1) * (m + 14) * P := Nat.mul_le_mul_left _ hP
  have h_c : s * ((4 * m + 40) * ((C + 1) * (j + 1) + 1) ^ s) ≤
      s * ((4 * m + 40) * ((C + 2) ^ s * P)) := by gcongr
  have h_f : (C + 2) ^ s * P ≤ (4 * m + 40) * ((C + 2) ^ s * P) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have h_g : (C + 1) * ((m + 12) * (j + 1) + 2) ≤ (C + 1) * (m + 14) * (n + 1) := by
    rw [mul_assoc]; gcongr; nlinarith
  have h_h : (m + 6) * xl ≤ (m + 6) * n := Nat.mul_le_mul_left _ hxl
  nlinarith

lemma succ_pow_le (n s : ℕ) : (n + 1) ^ s ≤ 2 ^ s * (n ^ s + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [zero_add, one_pow]; exact Nat.mul_pos (Nat.two_pow_pos s) (Nat.succ_pos _)
  · calc (n + 1) ^ s ≤ (2 * n) ^ s := Nat.pow_le_pow_left (by omega) s
      _ = 2 ^ s * n ^ s := mul_pow 2 n s
      _ ≤ 2 ^ s * (n ^ s + 1) := by gcongr; omega

lemma padDecider_decides (hs : 1 ≤ s) (y : List Bool) :
    ∃ t, t ≤ padK ML.symbols C s * (y.length + 1) ^ s ∧
      Lax119563.DeterministicTime.DecidesWithin (padDecider ML C s) y (y ∈ padLang ML C s) t := by
  rcases split_last_true y with ⟨x, j, rfl⟩ | ⟨n, rfl⟩
  · obtain ⟨s', ⟨t, ht, hr⟩, hH, hK⟩ := padPrep_runs_true (C := C) (s := s) x j
    have hans := thenClocked_answer hr hH hK
    refine ⟨_, ?_, _, hans, ?_⟩
    · have := padCost_le (m := ML.symbols) (C := C) hs (j := j) (xl := x.length)
        (n := (x ++ true :: List.replicate j false).length) (by simp; omega) (by simp)
      omega
    · constructor
      · intro h
        refine ⟨x, j, rfl, ?_⟩
        revert h
        rcases (runOn ML x (((C + 1) * (j + 1)) ^ s)).answer with _ | _ | _ <;> simp
      · rintro ⟨x', j', hy, hacc⟩
        obtain ⟨rfl, rfl⟩ := last_true_unique hy
        rw [hacc]; rfl
  · obtain ⟨s', ⟨t, ht, hr⟩, hH, hK⟩ := padPrep_runs_false (C := C) (s := s) (ML := ML) n
    have hans := thenClocked_answer hr hH hK
    refine ⟨_, ?_, _, hans, ?_⟩
    · have hP : n + 1 ≤ (n + 1) ^ s := Nat.le_self_pow (by omega) _
      simp only [List.length_replicate]
      calc t + 0 + 1 ≤ (2 * ML.symbols + 28) * (n + 1) := by nlinarith
        _ ≤ (2 * ML.symbols + 28) * (n + 1) ^ s := Nat.mul_le_mul_left _ hP
        _ ≤ padK ML.symbols C s * (n + 1) ^ s := Nat.mul_le_mul_right _
          (by unfold padK; exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
    · have h0 : (runOn ML [] 0).answer = none := rfl
      rw [h0]
      constructor
      · simp
      · rintro ⟨x', j', hy, -⟩
        have : true ∈ List.replicate n false := by rw [hy]; simp
        simp at this

theorem padLang_dt (ML : Machine) (C s : ℕ) (hs : 1 ≤ s) : DT (padLang ML C s) (s : ℝ) := by
  refine ⟨padDecider ML C s, thenClocked_deterministic _ _ _, padK ML.symbols C s * 2 ^ s,
    fun y => ?_⟩
  obtain ⟨t, ht, hd⟩ := padDecider_decides (ML := ML) (C := C) hs y
  refine decidesWithin_mono hd ?_
  apply Nat.le_floor
  have h1 := succ_pow_le y.length s
  have h2 : t ≤ padK ML.symbols C s * 2 ^ s * y.length ^ s + padK ML.symbols C s * 2 ^ s := by
    calc t ≤ padK ML.symbols C s * (y.length + 1) ^ s := ht
      _ ≤ padK ML.symbols C s * (2 ^ s * (y.length ^ s + 1)) := Nat.mul_le_mul_left _ h1
      _ = _ := by ring
  beta_reduce
  rw [Real.rpow_natCast]
  exact_mod_cast h2

end Spec

/-! ## Unpadding -/

section Unpad

variable (MP : Machine) (r : ℕ)

/-- Stack indices of the unpadding machine: scratch stacks after the tapes of `MP`. -/
def d2 (k : ℕ) (hk : k < 5 := by omega) : Fin (MP.tapes + 5 + 1) := ⟨MP.tapes + 1 + k, by omega⟩

/-- Write `x ++ [true] ++ 0^{|x|^r}` on stack `0`. -/
def unpadPrep : Prog (MP.tapes + 5 + 1) MP.symbols :=
  seq (moveCount 0 (d2 MP 0) (d2 MP 1))
    (seq (power (d2 MP 2) (d2 MP 1) (d2 MP 3) (d2 MP 4) r)
      (seq (moveAll (d2 MP 2) 0) (seq (push 0 1) (moveAll (d2 MP 0) 0))))

/-- Stacks in the shape used by `unpadPrep`. -/
def qst (a0 aA aN aP : List (Fin (MP.symbols + 2))) : Stacks (MP.tapes + 5 + 1) MP.symbols :=
  fun i => if i.val = 0 then a0 else if i.val = MP.tapes + 1 then aA else
    if i.val = MP.tapes + 2 then aN else if i.val = MP.tapes + 3 then aP else []

/-- Prove equalities between `qst` stacks and their updates. -/
macro "qst_eq" : tactic =>
  `(tactic| (funext i; simp only [qst, update_apply, Fin.ext_iff, Fin.val_zero, d2]; split_ifs <;>
    first | omega | rfl | simp_all))

/-- The cost bound of `unpadPrep`. -/
def unpadCost (m n r : ℕ) : ℕ :=
  (m + 8) * n + 1 + (r * ((4 * m + 40) * (n + 1) ^ r) + 3 + ((m + 6) * n ^ r + 1 + (2 +
    ((m + 6) * n + 1))))

variable {MP r}

lemma unpadPrep_runs (x : List Bool) :
    ∃ s', (unpadPrep MP r).RunsLe (inputStacks _ _ x) s' (unpadCost MP.symbols x.length r) ∧
      HandsOver MP s' (x ++ true :: List.replicate (x.length ^ r) false) := by
  have ne : ∀ a b : Fin (MP.tapes + 5 + 1), a.val ≠ b.val → a ≠ b :=
    fun a b h => Fin.ne_of_val_ne h
  set m := MP.symbols
  have hs0 : inputStacks (MP.tapes + 5) m x = qst MP (x.map (bitSym m)) [] [] [] := by
    funext i
    simp only [inputStacks, qst, Fin.ext_iff, Fin.val_zero]
    split_ifs <;> first | omega | rfl
  rw [hs0]
  have h1 : (moveCount 0 (d2 MP 0) (d2 MP 1) : Prog _ m).RunsLe (qst MP (x.map (bitSym m)) [] [] [])
      (qst MP [] (x.map (bitSym m)).reverse (unary m x.length) []) ((m + 8) * x.length + 1) :=
    (moveCount_runs (ne _ _ (by simp [d2])) (ne _ _ (by simp [d2])) (ne _ _ (by simp [d2]))
      (x.map (bitSym m)) _ (by simp [qst])).of_eq (by simp only [List.length_map]; qst_eq)
      (by simp)
  have h2 := power_runs (p := d2 MP 2) (n := d2 MP 1) (q := d2 MP 3) (h := d2 MP 4) (b := x.length)
    (ne _ _ (by simp [d2])) (ne _ _ (by simp [d2])) (ne _ _ (by simp [d2])) (ne _ _ (by simp [d2]))
    (ne _ _ (by simp [d2])) (ne _ _ (by simp [d2])) r
    (s := qst MP [] (x.map (bitSym m)).reverse (unary m x.length) [])
    (by simp [qst, d2]) (by simp [qst, d2]) (by simp [qst, d2]) (by simp [qst, d2])
  have h2' := h2.of_eq (s₂ := qst MP [] (x.map (bitSym m)).reverse (unary m x.length) (unary m (x.length ^ r)))
    (by qst_eq) le_rfl
  have h3 : (moveAll (d2 MP 2) 0 : Prog _ m).RunsLe
      (qst MP [] (x.map (bitSym m)).reverse (unary m x.length) (unary m (x.length ^ r)))
      (qst MP (unary m (x.length ^ r)) (x.map (bitSym m)).reverse (unary m x.length) []) ((m + 6) * x.length ^ r + 1) :=
    (moveAll_runs (ne _ _ (by simp [d2])) (unary m (x.length ^ r)) _ (by simp [qst, d2])).of_eq
      (by simp only [List.reverse_replicate]; qst_eq) (by simp)
  have h4 : (push 0 1 : Prog _ m).RunsLe
      (qst MP (unary m (x.length ^ r)) (x.map (bitSym m)).reverse (unary m x.length) [])
      (qst MP (1 :: unary m (x.length ^ r)) (x.map (bitSym m)).reverse (unary m x.length) []) 2 :=
    (RunsLe.push _ _ _).of_eq (by qst_eq) le_rfl
  have h5 : (moveAll (d2 MP 0) 0 : Prog _ m).RunsLe
      (qst MP (1 :: unary m (x.length ^ r)) (x.map (bitSym m)).reverse (unary m x.length) [])
      (qst MP ((x ++ true :: List.replicate (x.length ^ r) false).map (bitSym m)) [] (unary m x.length) [])
      ((m + 6) * x.length + 1) :=
    (moveAll_runs (ne _ _ (by simp [d2])) (x.map (bitSym m)).reverse _ (by simp [qst, d2])).of_eq
      (by simp only [List.reverse_reverse, List.map_append, List.map_cons, List.map_replicate];
          qst_eq) (by simp)
  refine ⟨_, h1.seq (h2'.seq (h3.seq (h4.seq h5))), fun i => ⟨fun hi => ?_, fun hi1 hi2 => ?_⟩⟩
  · simp only [qst]; split_ifs <;> first | omega | rfl
  · simp only [qst]; split_ifs <;> first | omega | rfl

end Unpad

end Lax119563Proofs.Hierarchy
