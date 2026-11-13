import Lax119563Proofs.Hierarchy.UnivTape

/-!
# One simulated step

`Rel M c s`: the stacks `s` of the simulator represent the configuration `c` of `M`.  One run
of `simStep` either reproduces a step of `M` (`simStep_next`) or records its answer
(`simStep_halt`), at cost quadratic in the size of the stacks.
-/

namespace Lax119563Proofs.Hierarchy.Universal

open Prog Function Lax489179.TuringMachine

/-- The stacks represent the (running) configuration `c`. -/
def Rel (M : Machine) (c : Config M) (s : Stacks 16 13) : Prop :=
  c.answer = none ∧ ∃ lefts rights : Fin (M.tapes + 1) → List ℕ,
    (∀ j, TapeRep (c.tape j) (c.head j) (lefts j) (rights j)) ∧
    s LS = records (List.ofFn lefts) ∧ s RS = records (List.ofFn rights) ∧
    s QS = List.replicate c.state.val tU ∧ s TBL = table M ∧
    ∀ i, i ≠ LS → i ≠ RS → i ≠ QS → i ≠ TBL → s i = []

/-- The size of the tape records. -/
def recSize (s : Stacks 16 13) : ℕ := (s LS).length + (s RS).length

/-- The cost bound of one simulated step. -/
def stepCost (Z : ℕ) : ℕ := 3000 * (Z + 1) ^ 2

lemma length_encL_reverse (l : List ℕ) : (encL l.reverse).length = (encL l).length := by
  simp [encL, List.length_flatMap, List.map_reverse, List.sum_reverse]

lemma encL_scanned_le : ∀ rs : List (List ℕ),
    (encL (rs.map scannedOf)).length ≤ (records rs).length
  | [] => by simp [encL, records]
  | r :: rs => by
    have := encL_scanned_le rs
    have h := length_encN_scanned_le r
    simp only [List.map_cons, encL_cons, records_cons, List.length_append] at this h ⊢
    omega

lemma entry_le_table : ∀ {es : List (List Tok × List Tok)} {e}, e ∈ es →
    (entryToks e).length ≤ (tableToks es).length
  | e' :: es, e, h => by
    rw [tableToks_cons, List.length_append]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := entry_le_table h; omega

lemma entryOf_le_table {M : Machine} (x : Key M) :
    (entryToks (entryOf M x)).length ≤ (table M).length :=
  entry_le_table (List.mem_map.mpr ⟨x, Finset.mem_toList.mpr (Finset.mem_univ x), rfl⟩)

lemma state_le_table {M : Machine} (q : Fin (M.states + 1)) : q.val + 1 ≤ (table M).length := by
  have := entryOf_le_table (M := M) (q, fun _ => 0)
  simp only [entryOf, entryToks, keyToks, List.length_append, length_encN, List.length_cons,
    List.length_nil] at this
  omega

lemma ins_le_table {M : Machine} (x : Key M) :
    (insOf M (M.transition x.1 x.2 false)).length ≤ (table M).length := by
  have := entryOf_le_table (M := M) x
  simp only [entryOf, entryToks, List.length_append, List.length_cons, List.length_reverse,
    List.length_nil] at this
  omega

lemma cost_arith (L R T q K : ℕ) (hq : q + 1 ≤ T) (hK : K ≤ q + 1 + R) :
    5 * cK * (R + q + 1) + 300 * (T + 1) * (K + 1) ≤ 2000 * (L + R + T + 1) ^ 2 := by
  have h1 : R + q + 1 ≤ 2 * (L + R + T + 1) := by omega
  have h2 : T + 1 ≤ L + R + T + 1 := by omega
  have h3 : K + 1 ≤ 2 * (L + R + T + 1) := by omega
  have h4 : 1 ≤ L + R + T + 1 := by omega
  have h5 : (T + 1) * (K + 1) ≤ (L + R + T + 1) * (2 * (L + R + T + 1)) := Nat.mul_le_mul h2 h3
  simp only [cK]
  nlinarith

lemma RunsLe.assoc {p q r : SProg} {s s' : Stacks 16 13} {T : ℕ}
    (h : (seq (seq p q) r).RunsLe s s' T) : (seq p (seq q r)).RunsLe s s' T := by
  obtain ⟨t, ht, h⟩ := h
  cases h with
  | seq h₁ h₂ =>
    cases h₁ with
    | seq h₃ h₄ => exact ⟨_, by omega, .seq h₃ (.seq h₄ h₂)⟩

section

variable {M : Machine} {c : Config M} {s : Stacks 16 13}

lemma scanned_eq {lefts rights : Fin (M.tapes + 1) → List ℕ}
    (hT : ∀ j, TapeRep (c.tape j) (c.head j) (lefts j) (rights j)) :
    (List.ofFn rights).map scannedOf = List.ofFn (fun j => (c.tape j (c.head j)).val) := by
  rw [List.map_ofFn]
  congr 1
  funext j
  have := (hT j).1 0
  simp only [Nat.cast_zero, add_zero] at this
  rw [this]
  simp only [comp_apply, scannedOf]
  cases rights j <;> rfl

/-- Building the key and looking it up. -/
lemma keyLookup_runs {lefts rights : Fin (M.tapes + 1) → List ℕ}
    (hT : ∀ j, TapeRep (c.tape j) (c.head j) (lefts j) (rights j))
    (hL : s LS = records (List.ofFn lefts)) (hR : s RS = records (List.ofFn rights))
    (hQ : s QS = List.replicate c.state.val tU) (hTb : s TBL = table M)
    (h0 : ∀ i, i ≠ LS → i ≠ RS → i ≠ QS → i ≠ TBL → s i = []) :
    (seq buildKey lookup).RunsLe s
      (update s INS (insOf M (M.transition c.state (fun j => c.tape j (c.head j)) false)))
      (2000 * (recSize s + (table M).length + 1) ^ 2) := by
  have h1 := buildKey_runs (List.ofFn rights) c.state.val s hR (h0 _ (by decide) (by decide)
    (by decide) (by decide)) (h0 _ (by decide) (by decide) (by decide) (by decide)) hQ
    (h0 _ (by decide) (by decide) (by decide) (by decide))
  set x : Key M := (c.state, fun j => c.tape j (c.head j))
  have hkey : keyOf c.state.val (List.ofFn rights) = (entryOf M x).1 := by
    have := scanned_eq hT
    simp only [keyOf_eq, this, entryOf, x]
  obtain ⟨es₁, es₂, hes, hne⟩ := entries_split x
  have h2 := lookup_runs (key := (entryOf M x).1) (ins := (entryOf M x).2) (es₁ := es₁)
    (es₂ := es₂) (keyToks_tokens _ _) (insOf_noE _) hne (update s KEY (keyOf c.state.val
      (List.ofFn rights))) (by simp only [update_self]; exact hkey)
    (by simp [h0 KEY2 (by decide) (by decide) (by decide) (by decide)])
    (by simp [h0 FLG (by decide) (by decide) (by decide) (by decide)])
    (by simp [h0 TBL2 (by decide) (by decide) (by decide) (by decide)])
    (by simp [hTb, table, hes])
  refine (h1.seq h2).of_eq ?_ ?_
  · funext k; fin_cases k <;>
      simp (config := {decide := true}) [update_apply, entryOf, x,
        h0 INS (by decide) (by decide) (by decide) (by decide),
        h0 KEY (by decide) (by decide) (by decide) (by decide)]
  · -- costs
    have e1 : (keyOf c.state.val (List.ofFn rights)).length ≤ c.state.val + 1 + (s RS).length := by
      rw [keyOf_eq, hR]
      simp only [keyToks, List.length_append, length_encN, length_encL_reverse]
      have := encL_scanned_le (List.ofFn rights)
      omega
    have e2 := state_le_table c.state
    have hR' : (records (List.ofFn rights)).length = (s RS).length := by rw [hR]
    rw [hR', ← hes, ← table, ← hkey]
    simp only [recSize]
    exact cost_arith _ _ _ _ _ e2 e1

lemma simStep_halt {b : Bool} (hR : Rel M c s)
    (htr : M.transition c.state (fun j => c.tape j (c.head j)) false = .halt b) :
    ∃ s', simStep.RunsLe s s' (stepCost (recSize s + (table M).length)) ∧
      s' DONE = [haltTok b] := by
  obtain ⟨-, lefts, rights, hT, hL, hR, hQ, hTb, h0⟩ := hR
  have h1 := keyLookup_runs hT hL hR hQ hTb h0
  rw [htr] at h1
  have h2 := apply_halt b (update s INS (insOf M (.halt b))) (by simp [insOf])
    (by simp [h0 DONE (by decide) (by decide) (by decide) (by decide)])
  refine ⟨_, RunsLe.assoc ((h1.seq h2).mono ?_), by simp⟩
  have : 1 ≤ (recSize s + (table M).length + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [stepCost]; omega

lemma simStep_next {q' : Fin (M.states + 1)} {w : Fin (M.tapes + 1) → Fin (M.symbols + 3)}
    {mv : Fin (M.tapes + 1) → Move} (hR : Rel M c s)
    (htr : M.transition c.state (fun j => c.tape j (c.head j)) false = .next q' w mv) :
    ∃ s', simStep.RunsLe s s' (stepCost (recSize s + (table M).length)) ∧
      Rel M (step M false c) s' ∧ recSize s' ≤ recSize s + (table M).length := by
  obtain ⟨hans, lefts, rights, hT, hL, hR, hQ, hTb, h0⟩ := hR
  have h1 := keyLookup_runs hT hL hR hQ hTb h0
  rw [htr] at h1
  set ts : List Tp := List.ofFn (fun j => (lefts j, rights j, (w j).val, mv j))
  have hins : insPart M w mv = insPairs ts := by
    simp only [insPart, insPairs, ts, List.flatMap_def, List.map_ofFn]; rfl
  set s₁ := update s INS (insOf M (.next q' w mv))
  have h2 := apply_next q'.val ts (List.replicate c.state.val tU) s₁
    (by simp [s₁, insOf, hins]) (by simp [s₁, hQ])
    (by simp [s₁, hL, ts, List.map_ofFn]; rfl) (by simp [s₁, hR, ts, List.map_ofFn]; rfl)
    (by simp [s₁, h0 TMP (by decide) (by decide) (by decide) (by decide)])
    (by simp [s₁, h0 LS2 (by decide) (by decide) (by decide) (by decide)])
    (by simp [s₁, h0 RS2 (by decide) (by decide) (by decide) (by decide)])
  have hstep : step M false c = ⟨q', fun j => c.head j + (mv j).offset,
      fun j z => if z = c.head j then w j else c.tape j z, none⟩ := by
    simp [Lax489179.TuringMachine.step, hans, htr]
  have hnl : newLefts ts = List.ofFn (fun j => (tapeUpd (lefts j) (rights j) (w j).val (mv j)).1) :=
    by simp [newLefts, ts, List.map_ofFn]; rfl
  have hnr : newRights ts =
      List.ofFn (fun j => (tapeUpd (lefts j) (rights j) (w j).val (mv j)).2) := by
    simp [newRights, ts, List.map_ofFn]; rfl
  refine ⟨_, RunsLe.assoc ((h1.seq h2).mono ?_),
    ⟨by rw [hstep], fun j => (tapeUpd (lefts j) (rights j) (w j).val (mv j)).1,
      fun j => (tapeUpd (lefts j) (rights j) (w j).val (mv j)).2, fun j => ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_⟩
  · -- cost
    have e1 := ins_le_table (M := M) (c.state, fun j => c.tape j (c.head j))
    rw [htr] at e1
    have e2 := state_le_table c.state
    have eL : (s₁ LS).length = (s LS).length := by simp [s₁]
    have eR : (s₁ RS).length = (s RS).length := by simp [s₁]
    have eI : (s₁ INS).length = (insOf M (.next q' w mv)).length := by simp [s₁]
    rw [eL, eR, eI]
    simp only [stepCost, recSize, cK, List.length_replicate] at *
    nlinarith
  · rw [hstep]; exact tapeRep_step (hT j) (w j) (mv j)
  · rw [hnl]; simp
  · rw [hnr]; simp
  · rw [hstep]; simp
  · simp [s₁, hTb]
  · intro i h1 h2 h3 h4
    fin_cases i <;> simp_all (config := {decide := true}) [update_apply, s₁]
  · -- size
    have e := newRecords_length ts
    have e1 := ins_le_table (M := M) (c.state, fun j => c.tape j (c.head j))
    rw [htr] at e1
    have : (insPairs ts).length ≤ (insOf M (.next q' w mv)).length := by
      simp [insOf, hins]; omega
    have eL : (records (ts.map (·.1))).length = (s LS).length := by
      rw [hL]; simp [ts, List.map_ofFn]; rfl
    have eR : (records (ts.map (·.2.1))).length = (s RS).length := by
      rw [hR]; simp [ts, List.map_ofFn]; rfl
    simp only [recSize]
    simp (config := {decide := true}) only [update_apply, if_true, if_false]
    omega

end

end Lax119563Proofs.Hierarchy.Universal
