import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Pi
import Lax119563Proofs.Hierarchy.UnivApply

/-!
# The transition table of a machine

For a machine `M` of the model, the table has one entry per pair `(q, c)` of a state and a
tuple of scanned symbols: the key `enc q ++ enc c_k ++ ⋯ ++ enc c_0` and the instruction
`δ(q, c, false)` in the token form used by `apply`.
-/

namespace Lax119563Proofs.Hierarchy.Universal

open Prog Function Lax489179.TuringMachine

/-- The tokens of a key with state `q` and scanned symbols `c = [c_0, …, c_k]`. -/
def keyToks (q : ℕ) (c : List ℕ) : List Tok := encN q ++ encL c.reverse

lemma keyOf_eq (q : ℕ) (rs : List (List ℕ)) : keyOf q rs = keyToks q (rs.map scannedOf) := by
  simp only [keyOf, keyToks, encL, List.flatMap_def, List.map_reverse, List.map_map]
  rfl

lemma encN_cancel : ∀ {a b : ℕ} {l l' : List Tok}, encN a ++ l = encN b ++ l' → a = b ∧ l = l'
  | 0, 0, l, l', h => by simpa [encN] using h
  | 0, b + 1, l, l', h => by simp [encN, List.replicate_succ] at h
  | a + 1, 0, l, l', h => by simp [encN, List.replicate_succ] at h
  | a + 1, b + 1, l, l', h => by
    simp only [encN, List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    have := encN_cancel (a := a) (b := b) (l := l) (l' := l') (by simpa [encN] using h)
    exact ⟨by omega, this.2⟩

lemma encL_cons (c : ℕ) (l : List ℕ) : encL (c :: l) = encN c ++ encL l := by simp [encL]

lemma encL_inj : ∀ {l l' : List ℕ}, encL l = encL l' → l = l'
  | [], [], _ => rfl
  | [], c :: l, h => by simp [encL, encN] at h
  | c :: l, [], h => by simp [encL, encN] at h
  | c :: l, c' :: l', h => by
    rw [encL_cons, encL_cons] at h
    obtain ⟨rfl, h'⟩ := encN_cancel h
    rw [encL_inj h']

lemma keyToks_inj {q q' : ℕ} {c c' : List ℕ} (h : keyToks q c = keyToks q' c') :
    q = q' ∧ c = c' := by
  obtain ⟨rfl, h'⟩ := encN_cancel h
  exact ⟨rfl, List.reverse_injective (encL_inj h')⟩

lemma keyToks_tokens (q : ℕ) (c : List ℕ) : ∀ t ∈ keyToks q c, t = tU ∨ t = tS := by
  intro t ht
  simp only [keyToks, encL, encN, List.mem_append, List.mem_flatMap, List.mem_replicate,
    List.mem_singleton] at ht
  rcases ht with (⟨_, h⟩ | h) | ⟨_, _, (⟨_, h⟩ | h)⟩ <;> simp [h]

variable (M : Machine)

/-- Keys of the table. -/
abbrev Key := Fin (M.states + 1) × (Fin (M.tapes + 1) → Fin (M.symbols + 3))

/-- The tokens of the write/move part of an instruction. -/
def insPart (w : Fin (M.tapes + 1) → Fin (M.symbols + 3)) (mv : Fin (M.tapes + 1) → Move) :
    List Tok :=
  (List.ofFn fun j => encN (w j).val ++ [mvTok (mv j)]).flatten

/-- The tokens of an instruction. -/
def insOf : Instruction (M.tapes + 1) (M.symbols + 3) (M.states + 1) → List Tok
  | .halt b => [haltTok b]
  | .next q w mv => tN :: (encN q.val ++ insPart M w mv)

/-- The table entry of a key. -/
def entryOf (x : Key M) : List Tok × List Tok :=
  (keyToks x.1.val (List.ofFn fun j => (x.2 j).val), insOf M (M.transition x.1 x.2 false))

/-- The entries of the table. -/
noncomputable def entries : List (List Tok × List Tok) :=
  (Finset.univ : Finset (Key M)).toList.map (entryOf M)

/-- The table. -/
noncomputable def table : List Tok := tableToks (entries M)

variable {M}

lemma insOf_noE (i : Instruction (M.tapes + 1) (M.symbols + 3) (M.states + 1)) :
    tE ∉ insOf M i := by
  cases i with
  | halt b => cases b <;> simp [insOf, haltTok]
  | next q w mv =>
    simp only [insOf, insPart, encN, List.mem_cons, List.mem_append, List.mem_replicate,
      List.mem_flatten, List.mem_ofFn, List.mem_singleton, not_or]
    refine ⟨by decide, ⟨fun h => absurd h.2 (by decide), by decide⟩, ?_⟩
    rintro ⟨l, ⟨j, rfl⟩, h⟩
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at h
    rcases h with (⟨_, h⟩ | h) | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · rcases hmv : mv j <;> simp [mvTok, hmv] at h

lemma entryOf_wf (x : Key M) : WellFormed (entryOf M x) :=
  ⟨keyToks_tokens _ _, insOf_noE _⟩

lemma entryOf_key_inj {x y : Key M} (h : (entryOf M x).1 = (entryOf M y).1) : x = y := by
  obtain ⟨h1, h2⟩ := keyToks_inj h
  have h2' : (fun j => (x.2 j).val) = fun j => (y.2 j).val := List.ofFn_injective h2
  ext1
  · exact Fin.ext h1
  · funext j; exact Fin.ext (congrFun h2' j)

lemma entries_split (x : Key M) :
    ∃ es₁ es₂, entries M = es₁ ++ entryOf M x :: es₂ ∧
      ∀ e ∈ es₁, WellFormed e ∧ e.1 ≠ (entryOf M x).1 := by
  obtain ⟨s, t, hst⟩ := List.append_of_mem (Finset.mem_toList.mpr (Finset.mem_univ x))
  have hnd := Finset.nodup_toList (Finset.univ : Finset (Key M))
  rw [hst] at hnd
  have hx : x ∉ s := by
    intro hm
    have := List.nodup_append.mp hnd
    exact this.2.2 x hm x List.mem_cons_self rfl
  refine ⟨s.map (entryOf M), t.map (entryOf M), by simp [entries, hst], ?_⟩
  intro e he
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp he
  exact ⟨entryOf_wf y, fun h => hx (entryOf_key_inj h ▸ hy)⟩

end Lax119563Proofs.Hierarchy.Universal
