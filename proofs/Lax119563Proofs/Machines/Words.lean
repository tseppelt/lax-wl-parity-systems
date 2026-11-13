import Lax119563Proofs.Machines.Compile

/-!
# Tapes holding words

`Tape.ofWord pre rest` is the tape whose cells hold `pre ++ rest` from position `0` (blanks
elsewhere) with the head on position `|pre|`, i.e. on the first symbol of `rest` (or on the
blank after the word if `rest = []`). The lemmas below describe the effect of single
transitions on such tapes.
-/

open Lax489179.TuringMachine (Move)

namespace Lax119563Proofs.Machines

variable {Γ : Type} [TapeAlphabet Γ]

/-! ## Cells of a list -/

lemma listCells_natCast (l : List Γ) (n : ℕ) : listCells l (n : ℤ) = l[n]?.getD blank := by
  simp [listCells]

lemma listCells_of_neg (l : List Γ) {z : ℤ} (hz : z < 0) : listCells l z = blank := by
  simp [listCells, not_le.mpr hz]

lemma listCells_ext {l₁ l₂ : List Γ}
    (h : ∀ n : ℕ, l₁[n]?.getD blank = l₂[n]?.getD blank) : listCells l₁ = listCells l₂ := by
  funext z
  unfold listCells
  split_ifs
  · exact h _
  · rfl

@[simp] lemma listCells_nil : listCells ([] : List Γ) = fun _ => blank := by
  funext z; simp [listCells]

lemma listCells_append_blank (l : List Γ) : listCells (l ++ [blank]) = listCells l := by
  apply listCells_ext
  intro n
  rcases lt_trichotomy n l.length with h | rfl | h
  · simp [List.getElem?_append_left h]
  · simp
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt h
    rw [List.getElem?_append_right (by omega),
      List.getElem?_eq_none (l := l) (by omega), show l.length + j + 1 - l.length = j + 1 by omega]
    simp

lemma update_listCells {l l' : List Γ} {n : ℕ} {b : Γ}
    (h : ∀ m : ℕ, l'[m]?.getD blank = if m = n then b else l[m]?.getD blank) :
    Function.update (listCells l) (n : ℤ) b = listCells l' := by
  funext z
  rw [Function.update_apply]
  by_cases hz : 0 ≤ z
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hz
    rw [listCells_natCast, listCells_natCast, h m]
    simp only [Nat.cast_inj]
  · have hzn : z ≠ (n : ℤ) := by omega
    rw [if_neg hzn, listCells_of_neg _ (by omega), listCells_of_neg _ (by omega)]

/-- Overwriting position `|pre|` of `pre ++ rest`. -/
lemma getD_set_mid (pre rest : List Γ) (b : Γ) (m : ℕ) :
    (pre ++ b :: rest.tail)[m]?.getD blank =
      if m = pre.length then b else (pre ++ rest)[m]?.getD blank := by
  rcases lt_trichotomy m pre.length with h | rfl | h
  · rw [if_neg (by omega), List.getElem?_append_left h, List.getElem?_append_left h]
  · simp
  · rw [if_neg (by omega), List.getElem?_append_right (by omega),
      List.getElem?_append_right (by omega)]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt h
    rw [show pre.length + j + 1 - pre.length = j + 1 by omega, List.getElem?_cons_succ]
    cases rest <;> simp

/-! ## Word tapes -/

/-- The tape holding `pre ++ rest` from position `0`, with the head on position `|pre|`. -/
def Tape.ofWord (pre rest : List Γ) : Tape Γ := ⟨pre.length, listCells (pre ++ rest)⟩

namespace Tape

@[simp] lemma ofWord_head (pre rest : List Γ) : (ofWord pre rest).head = pre.length := rfl

@[simp] lemma ofWord_cells (pre rest : List Γ) :
    (ofWord pre rest).cells = listCells (pre ++ rest) := rfl

lemma read_ofWord (pre rest : List Γ) : (ofWord pre rest).read = rest.headD blank := by
  simp only [read, ofWord, listCells_natCast]
  cases rest <;> simp

@[simp] lemma read_ofWord_cons (pre rest : List Γ) (a : Γ) :
    (ofWord pre (a :: rest)).read = a := by simp [read_ofWord]

@[simp] lemma read_ofWord_nil (pre : List Γ) : (ofWord pre []).read = blank := by
  simp [read_ofWord]

lemma ofWord_append_blank (pre rest : List Γ) :
    ofWord pre (rest ++ [blank]) = ofWord pre rest := by
  simp only [ofWord, ← List.append_assoc, listCells_append_blank]

lemma ofWord_nil_blank (pre : List Γ) : ofWord pre [blank] = ofWord pre [] := by
  simpa using ofWord_append_blank pre []

lemma ofWord_eq_ofWord_append (pre rest : List Γ) : ofWord pre rest =
    ⟨pre.length, listCells (pre ++ rest)⟩ := rfl

/-- Writing and moving right. -/
lemma act_ofWord_right (pre rest : List Γ) (b : Γ) :
    (ofWord pre rest).act b .right = ofWord (pre ++ [b]) rest.tail := by
  ext
  · simp
  · simp only [act_cells, ofWord_cells, ofWord_head]
    rw [update_listCells (l' := pre ++ [b] ++ rest.tail)]
    intro m
    rw [List.append_assoc, List.singleton_append]
    exact getD_set_mid pre rest b m

/-- Writing without moving. -/
lemma act_ofWord_stay (pre rest : List Γ) (b : Γ) :
    (ofWord pre rest).act b .stay = ofWord pre (b :: rest.tail) := by
  ext
  · simp
  · simp only [act_cells, ofWord_cells, ofWord_head]
    exact congrFun (update_listCells (getD_set_mid pre rest b)) _

/-- Writing and moving left. -/
lemma act_ofWord_left (pre rest : List Γ) (a b : Γ) :
    (ofWord (pre ++ [a]) rest).act b .left = ofWord pre (a :: b :: rest.tail) := by
  ext
  · simp
  · simp only [act_cells, ofWord_cells, ofWord_head]
    rw [update_listCells (l' := pre ++ a :: b :: rest.tail)]
    intro m
    have := getD_set_mid (pre ++ [a]) rest b m
    simpa using this

lemma move_ofWord_right (pre rest : List Γ) (a : Γ) :
    (ofWord pre (a :: rest)).move .right = ofWord (pre ++ [a]) rest := by
  ext <;> simp

lemma move_ofWord_left (pre rest : List Γ) (a : Γ) :
    (ofWord (pre ++ [a]) rest).move .left = ofWord pre (a :: rest) := by
  ext <;> simp

end Tape

end Lax119563Proofs.Machines
