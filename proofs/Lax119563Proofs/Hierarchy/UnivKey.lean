import Mathlib.Tactic.FinCases
import Lax119563Proofs.Hierarchy.UnivSim

/-!
# Encodings of configurations, and building the key

Symbols are natural numbers encoded in unary (`encN n = U^n S`); a tape record is a list of
encoded symbols followed by `R`.  `buildKey` pushes on `KEY` the encoded scanned symbols of all
records of `RS` (last record first) and then the encoded state.
-/

namespace Lax119563Proofs.Hierarchy.Universal

open Prog Function

/-- The unary encoding of a number. -/
def encN (n : ℕ) : List Tok := List.replicate n tU ++ [tS]

/-- The encoding of a list of numbers. -/
def encL (l : List ℕ) : List Tok := l.flatMap encN

/-- A tape record. -/
def record (l : List ℕ) : List Tok := encL l ++ [tR]

/-- The encoding of a list of records. -/
def records (rs : List (List ℕ)) : List Tok := rs.flatMap record

lemma tS_not_mem_rep (n : ℕ) : tS ∉ List.replicate n tU := by
  simp only [List.mem_replicate]; intro h; exact absurd h.2 (by decide)

lemma tR_not_mem_encL (l : List ℕ) : tR ∉ encL l := by
  simp only [encL, encN, List.mem_flatMap, List.mem_append, List.mem_replicate, List.mem_singleton,
    not_exists, not_and, not_or]
  intro x _; exact ⟨fun _ => by decide, by decide⟩

@[simp] lemma length_encN (n : ℕ) : (encN n).length = n + 1 := by simp [encN]

@[simp] lemma length_record (l : List ℕ) : (record l).length = (encL l).length + 1 := by
  simp [record]

/-- The key contribution of a right part: its first symbol, blank if empty. -/
def scannedOf (r : List ℕ) : ℕ := r.headD 0

/-- Shorthand for the cost constant of symbol transfers. -/
abbrev cK : ℕ := 100

lemma copyScanned_runs (r : List ℕ) (rest : List (List ℕ)) (s : Stacks 16 13) (hs : s RS = record r ++ records rest)
    (hT : s TMP = []) :
    copyScanned.RunsLe s (update s KEY (encN (scannedOf r) ++ s KEY))
      (cK * ((encN (scannedOf r)).length + 1)) := by
  cases r with
  | nil =>
    refine ((RunsLe.push KEY tS s).iteT (by simp [tops, hs, record, encL, isTop])).of_eq ?_
      (by simp [scannedOf, cK])
    simp [scannedOf, encN]
  | cons c r =>
    have hs' : s RS = List.replicate c tU ++ tS :: (encL r ++ [tR] ++ records rest) := by
      rw [hs]; simp [record, encL, encN]
    have h1 := moveThrough_runs (i := RS) (j := TMP) (by decide) (tS_not_mem_rep c) hs'
    rw [hT, List.append_nil] at h1
    have h2 := dupAll_runs (i := TMP) (j := RS) (k := KEY) (by decide) (by decide) (by decide)
      (tS :: (List.replicate c tU).reverse)
      (update (update s RS (encL r ++ [tR] ++ records rest)) TMP (tS :: (List.replicate c tU).reverse))
      (by simp)
    have hc : isTop RS tR (tops s) = false := by
      cases c <;> simp [tops, hs', isTop, List.replicate_succ] <;> decide
    refine ((h1.seq h2).iteF hc).of_eq ?_ ?_
    · clear h1 h2 hc
      simp only [List.reverse_cons, List.reverse_reverse, List.reverse_replicate, scannedOf,
        List.headD_cons, encN]
      funext k
      simp only [update_apply]
      split_ifs <;> simp_all (config := { decide := true }) [record, encL, encN]
    · simp only [scannedOf, List.headD_cons, length_encN, List.length_cons, List.length_reverse,
        List.length_replicate]
      nlinarith

/-- Prove equalities between updated simulator stacks. -/
macro "sim_eq" : tactic =>
  `(tactic| (funext k; fin_cases k <;> simp_all (config := {decide := true}) [Function.update_apply]))

lemma length_encN_scanned_le (r : List ℕ) : (encN (scannedOf r)).length ≤ (record r).length := by
  cases r with
  | nil => simp [scannedOf, record, encL]
  | cons c r => simp [scannedOf, record, encL]

lemma records_cons (r : List ℕ) (rs : List (List ℕ)) :
    records (r :: rs) = record r ++ records rs := by simp [records]

lemma length_le_records (rs : List (List ℕ)) : rs.length ≤ (records rs).length := by
  induction rs with
  | nil => simp
  | cons r rs ih => simp [records_cons]; omega

/-- The loop of `buildKey`. -/
def keyLoop : SProg := loop (nonempty RS) (seq copyScanned (moveThrough RS RS2 tR))

lemma keyLoop_runs :
    ∀ (rs : List (List ℕ)) (s : Stacks 16 13), s RS = records rs → s TMP = [] →
      keyLoop.RunsLe s (update (update (update s RS []) RS2 ((records rs).reverse ++ s RS2)) KEY
        ((rs.map (fun r => encN (scannedOf r))).reverse.flatten ++ s KEY))
        (4 * cK * (records rs).length + 1)
  | [], s, hs, _ =>
    (RunsLe.loopF (c := nonempty RS) (s := s) (p := seq copyScanned (moveThrough RS RS2 tR))
      (by simp [tops, hs, nonempty, records])).of_eq (by simp [records] at hs; sim_eq)
      (by simp)
  | r :: rs, s, hs, hT => by
    rw [records_cons] at hs
    have h1 := copyScanned_runs r rs s hs hT
    set s₁ := update s KEY (encN (scannedOf r) ++ s KEY)
    have hs₁ : s₁ RS = encL r ++ tR :: records rs := by simp (config := {decide := true}) [Function.update_apply, s₁, hs, record]
    have h2 := moveThrough_runs (i := RS) (j := RS2) (by decide) (tR_not_mem_encL r) hs₁
    set s₂ := update (update s₁ RS (records rs)) RS2 (tR :: ((encL r).reverse ++ s₁ RS2))
    have h3 := keyLoop_runs rs s₂ (by simp (config := {decide := true}) [Function.update_apply, s₂]) (by simp (config := {decide := true}) [Function.update_apply, s₂, s₁, hT])
    have hc : nonempty RS (tops s) = true := by
      cases r <;> simp [tops, hs, nonempty, record, encL, encN] <;> cases ‹ℕ› <;> simp
    refine (RunsLe.loopT hc (h1.seq h2) h3).of_eq ?_ ?_
    · simp only [s₂, s₁, records_cons, record, List.map_cons, List.reverse_cons,
        List.flatten_append, List.reverse_append, List.append_assoc]
      sim_eq
    · have := length_encN_scanned_le r
      simp only [records_cons, List.length_append, length_record] at this ⊢
      nlinarith

/-- The key of a configuration: the encoded state and the scanned symbols (last tape first). -/
def keyOf (q : ℕ) (rs : List (List ℕ)) : List Tok :=
  encN q ++ (rs.map (fun r => encN (scannedOf r))).reverse.flatten

lemma buildKey_runs (rs : List (List ℕ)) (q : ℕ) (s : Stacks 16 13) (hs : s RS = records rs)
    (hT : s TMP = []) (hR2 : s RS2 = []) (hQ : s QS = List.replicate q tU) (hK : s KEY = []) :
    buildKey.RunsLe s (update s KEY (keyOf q rs)) (5 * cK * ((records rs).length + q + 1)) := by
  have h1 := keyLoop_runs rs s hs hT
  set s₁ := update (update (update s RS []) RS2 ((records rs).reverse ++ s RS2)) KEY
    ((rs.map (fun r => encN (scannedOf r))).reverse.flatten ++ s KEY)
  have h2 := moveAll_runs (i := RS2) (j := RS) (by decide) ((records rs).reverse) s₁
    (by simp (config := {decide := true}) [Function.update_apply, s₁, hR2])
  set s₂ := update (update s₁ RS2 []) RS ((records rs).reverse.reverse ++ s₁ RS)
  have h3 := RunsLe.push KEY tS s₂
  set s₃ := update s₂ KEY (tS :: s₂ KEY)
  have h4 := dupAll_runs (i := QS) (j := TMP) (k := KEY) (by decide) (by decide) (by decide)
    (List.replicate q tU) s₃ (by simp (config := {decide := true}) [Function.update_apply, s₃, s₂, s₁, hQ])
  set s₄ := update (update (update s₃ QS []) TMP ((List.replicate q tU).reverse ++ s₃ TMP)) KEY
    ((List.replicate q tU).reverse ++ s₃ KEY)
  have h5 := moveAll_runs (i := TMP) (j := QS) (by decide) (List.replicate q tU) s₄
    (by simp (config := {decide := true}) [Function.update_apply, s₄, s₃, s₂, s₁, hT])
  refine (h1.seq (h2.seq (h3.seq (h4.seq h5)))).of_eq ?_ ?_
  · simp only [s₄, s₃, s₂, s₁, keyOf, encN, List.reverse_reverse, List.reverse_replicate]
    sim_eq
  · simp only [List.length_reverse, List.length_replicate]
    nlinarith

end Lax119563Proofs.Hierarchy.Universal
