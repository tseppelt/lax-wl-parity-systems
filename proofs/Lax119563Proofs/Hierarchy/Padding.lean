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

end Spec

end Lax119563Proofs.Hierarchy
