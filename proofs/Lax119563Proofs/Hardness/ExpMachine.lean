import Lax119563Proofs.Hardness.LeadMachine
import Lax119563Proofs.Machines.Extras

/-!
# The machines of the EXPTIME reduction

* `dropTM`: a machine computing `x` from `true :: true :: x` (`drop_computesWithin`). Composed
  with a decider of a language `L`, it decides `L` on padded inputs `true :: true :: x`, which
  have length at least `2`, as the pipeline requires.
* `redTM R d`: on input `x` with `n = |x|` and `L = |bits n|`, it counts `n` in binary, writes
  `encodeNats [h, h] ++ true :: true :: x` with `h = 2^(d (L + 1)) - 1` (the code of `h` is
  `(1 1)^(d (L+1)) 0`, written with `d` passes over the counter), and runs the machine `R` on
  it (by `simTM`). So if `R` computes `z` from that word within `t` steps, `redTM R d`
  computes `z` from `x` within `2 t + 40 (d + 1) (n + 1)^2` steps (`redTM_computesWithin`).
-/

open Lax489179.TuringMachine (Machine Config Move Instruction init step run Deterministic)
open Lax119563.DeterministicTime Lax119563.BinaryEncodings

namespace Lax119563Proofs.Hardness

open Machines Machines.TM Function

/-! ## Writing runs of ones -/

section Ones

variable {Γ : Type} [TapeAlphabet Γ] [DecidableEq Γ] {k : ℕ}

/-- `n`-fold repetition of a machine. -/
def rep (M : TM k Γ) : ℕ → TM k Γ
  | 0 => nop
  | n + 1 => M ;; rep M n

/-- For each symbol of the counter tape `c`, append two ones to tape `o`. -/
def onesLoop (c o : Fin k) : TM k Γ :=
  loop (fun s => decide (s c ≠ blank))
    (act₂ c o (fun a _ => ((a, .right), (bit true, .right))) ;; writeR o (bit true))

/-- Append `2 (|u| + 1)` ones to tape `o`, where `u` is the word on the counter tape. -/
def pass (c o : Fin k) : TM k Γ :=
  writeR o (bit true) ;; writeR o (bit true) ;; onesLoop c o ;; rewind c

/-- Append the code of `2^(m (|u| + 1)) - 1`. -/
def emitOnes (c o : Fin k) (m : ℕ) : TM k Γ :=
  rep (pass c o) m ;; writeR o (bit false)

theorem onesLoop_ofWord {c o : Fin k} (hco : c ≠ o) (u : List Γ) (hu : ∀ a ∈ u, a ≠ blank) :
    ∀ (pre opre : List Γ) (T : Tapes k Γ), T c = .ofWord pre u → T o = .ofWord opre [] →
    (onesLoop c o).RunsWithin T (3 * u.length)
      (update (update T c (.ofWord (pre ++ u) [])) o
        (.ofWord (opre ++ List.replicate (2 * u.length) (bit true)) [])) := by
  induction u with
  | nil =>
    intro pre opre T hc ho
    refine ((loop_runsWithin_exit (by simp [readAll, hc])).mono (by simp)).congr_right ?_
    funext l
    by_cases hl : l = o
    · subst hl; simp [ho]
    · by_cases hl' : l = c
      · subst hl'; simp [update_of_ne hl, hc]
      · simp [update_of_ne hl, update_of_ne hl']
  | cons a u ih =>
    intro pre opre T hc ho
    have ha : a ≠ blank := hu a (by simp)
    have h₁ := act₂_runsWithin hco (fun a (_ : Γ) => ((a, Move.right), (bit true, Move.right))) T
    simp only [hc, ho, Tape.read_ofWord_cons, Tape.act_ofWord_right, List.tail_cons,
      List.tail_nil] at h₁
    have h₂ := writeR_runsWithin o (bit true)
      (update (update T c (Tape.ofWord (pre ++ [a]) u)) o (Tape.ofWord (opre ++ [bit true]) []))
    simp only [update_self, Tape.act_ofWord_right, List.tail_nil, update_idem] at h₂
    have h₃ := ih (fun b hb => hu b (by simp [hb])) (pre ++ [a]) (opre ++ [bit true] ++ [bit true])
      (update (update T c (Tape.ofWord (pre ++ [a]) u)) o
        (Tape.ofWord (opre ++ [bit true] ++ [bit true]) []))
      (by simp [update_of_ne hco]) (by simp)
    have h := loop_runsWithin_iter (c := fun s => decide (s c ≠ blank))
      (by simp [readAll, hc, ha]) (seq_runsWithin h₁ h₂) h₃
    refine (h.mono (by simp; omega)).congr_right ?_
    rw [update_update_update_update hco]
    congr 2
    · simp
    · simp only [List.append_assoc, List.length_cons]
      congr 1

theorem pass_ofWord {c o : Fin k} (hco : c ≠ o) (u : List Γ) (hu : ∀ a ∈ u, a ≠ blank)
    (opre : List Γ) (T : Tapes k Γ) (hc : T c = .ofWord [] u) (ho : T o = .ofWord opre []) :
    (pass c o).RunsWithin T (5 * u.length + 4)
      (update T o (.ofWord (opre ++ List.replicate (2 * (u.length + 1)) (bit true)) [])) := by
  have h₁ := writeR_runsWithin o (bit true) T
  rw [ho, Tape.act_ofWord_right] at h₁
  have h₂ := writeR_runsWithin o (bit true) (update T o (Tape.ofWord (opre ++ [bit true]) []))
  simp only [update_self, Tape.act_ofWord_right, List.tail_nil, update_idem] at h₂
  have h₃ := onesLoop_ofWord hco u hu [] (opre ++ [bit true] ++ [bit true])
    (update T o (Tape.ofWord (opre ++ [bit true] ++ [bit true]) []))
    (by simp [update_of_ne hco, hc]) (by simp)
  have h₄ := rewind_ofWord c (pre := u) (rest := [])
    (T := update (update (update T o (Tape.ofWord (opre ++ [bit true] ++ [bit true]) [])) c
      (Tape.ofWord ([] ++ u) [])) o
      (Tape.ofWord (opre ++ [bit true] ++ [bit true] ++ List.replicate (2 * u.length) (bit true)) []))
    (by simp [update_of_ne hco]) hu
  refine ((seq_runsWithin (seq_runsWithin (seq_runsWithin h₁ h₂) h₃) h₄).mono
    (by omega)).congr_right ?_
  funext l
  by_cases hl : l = o
  · subst hl
    simp only [update_of_ne hco.symm, update_self, List.append_assoc]
    congr 2
  · by_cases hl' : l = c
    · subst hl'; simp [update_of_ne hl, hc]
    · simp [update_of_ne hl, update_of_ne hl']

theorem rep_pass_ofWord {c o : Fin k} (hco : c ≠ o) (u : List Γ) (hu : ∀ a ∈ u, a ≠ blank) :
    ∀ (m : ℕ) (opre : List Γ) (T : Tapes k Γ), T c = .ofWord [] u → T o = .ofWord opre [] →
    (rep (pass c o) m).RunsWithin T (m * (5 * u.length + 4))
      (update T o (.ofWord (opre ++ List.replicate (2 * m * (u.length + 1)) (bit true)) [])) := by
  intro m
  induction m with
  | zero =>
    intro opre T hc ho
    refine ((nop_haltsIn T).runsWithin.mono (by simp)).congr_right ?_
    simp [← ho]
  | succ m ih =>
    intro opre T hc ho
    have h₁ := pass_ofWord hco u hu opre T hc ho
    have h₂ := ih (opre ++ List.replicate (2 * (u.length + 1)) (bit true))
      (update T o (.ofWord (opre ++ List.replicate (2 * (u.length + 1)) (bit true)) []))
      (by simp [update_of_ne hco, hc]) (by simp)
    refine ((seq_runsWithin h₁ h₂).mono (le_of_eq (by ring))).congr_right ?_
    rw [update_idem, List.append_assoc, ← List.replicate_add,
      show 2 * (u.length + 1) + 2 * m * (u.length + 1) = 2 * (m + 1) * (u.length + 1) by ring]

theorem emitOnes_ofWord {c o : Fin k} (hco : c ≠ o) (u : List Γ) (hu : ∀ a ∈ u, a ≠ blank)
    (m : ℕ) (opre : List Γ) (T : Tapes k Γ) (hc : T c = .ofWord [] u)
    (ho : T o = .ofWord opre []) :
    (emitOnes c o m).RunsWithin T (m * (5 * u.length + 4) + 1)
      (update T o (.ofWord (opre ++ (List.replicate (2 * m * (u.length + 1)) (bit true) ++
        [bit false])) [])) := by
  have h₁ := rep_pass_ofWord hco u hu m opre T hc ho
  have h₂ := writeR_runsWithin o (bit false)
    (update T o (Tape.ofWord (opre ++ List.replicate (2 * m * (u.length + 1)) (bit true)) []))
  simp only [update_self, Tape.act_ofWord_right, List.tail_nil, update_idem] at h₂
  exact (seq_runsWithin h₁ h₂).congr_right (by simp)

end Ones

/-! ## The number `h` -/

lemma bits_two_pow_sub_one (j : ℕ) : Nat.bits (2 ^ j - 1) = List.replicate j true := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : 2 ^ (j + 1) - 1 = 2 * (2 ^ j - 1) + 1 := by
      have := Nat.one_le_two_pow (n := j); rw [pow_succ]; omega
    rw [e, Nat.bit1_bits, ih, List.replicate_succ]

lemma encodeNat_two_pow_sub_one (j : ℕ) :
    encodeNat (2 ^ j - 1) = List.replicate (2 * j) true ++ [false] := by
  rw [encodeNat, bits_two_pow_sub_one]
  congr 1
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ, List.flatMap_cons, ih,
      show 2 * (j + 1) = 1 + 1 + 2 * j by ring, List.replicate_add, List.replicate_add]
    simp

/-- The horizon exponent `h = 2^(d (|bits n| + 1)) - 1`. -/
def hOf (d n : ℕ) : ℕ := 2 ^ (d * ((Nat.bits n).length + 1)) - 1

/-! ## Dropping two leading bits -/

/-- The core of the machine dropping the two leading bits. -/
def dropTM : TM 2 (Fin 3) :=
  moveR 0 ;; moveR 0 ;; copyR 0 1 (fun a => decide (a ≠ blank))

/-- The machine computing `x` from `true :: true :: x`. -/
noncomputable def dropMachine : Machine := (dropTM ;; finish 1).compile

theorem drop_computesWithin (x : List Bool) :
    ComputesWithin dropMachine (true :: true :: x) x (8 * x.length + 11) := by
  set X : List (Fin 3) := bitsWord x with hX
  set T0 := inputTapes (Γ := Fin 3) 1 (true :: true :: x) with hT0
  have h00 : T0 0 = .ofWord [] (bit true :: bit true :: X) := by
    rw [hT0, inputTapes_zero]; simp [bitsWord, hX]
  have h01 : T0 1 = .ofWord [] [] := inputTapes_ne_zero _ (by decide)
  have h₁ := moveR_runsWithin 0 T0
  rw [h00, Tape.move_ofWord_right] at h₁
  have h₂ := moveR_runsWithin 0 (update T0 0 (Tape.ofWord [bit true] (bit true :: X)))
  simp only [update_self, Tape.move_ofWord_right, update_idem, List.singleton_append] at h₂
  have h₃ := copyR_ofWord (show (0 : Fin 2) ≠ 1 by decide) (fun a => decide (a ≠ blank))
    (T := update T0 0 (Tape.ofWord [bit true, bit true] X)) (pre := [bit true, bit true])
    (u := X) (rest := []) (dpre := []) (drest := []) (by simp)
    (fun a ha => by simpa using bit_ne_blank_of_mem_bitsWord ha) (by simp)
    (by simp [h01])
  have h := seq_runsWithin (seq_runsWithin h₁ h₂) h₃
  have hc := TM.computesWithin_finish dropTM (o := 1) (by decide) (x := true :: true :: x) (y := x)
    h (pre := [bit true, bit true] ++ X) (rest := []) (opre := X) (orest := [])
    (by simp)
    (fun a ha => by
      simp only [List.append_nil, List.mem_append, List.mem_cons, List.mem_nil_iff,
        or_false] at ha
      rcases ha with (rfl | rfl) | ha
      · simp
      · simp
      · exact bit_ne_blank_of_mem_bitsWord ha)
    (by simp) (by simp [hX])
  refine Main.Compose.computesWithin_mono' hc ?_
  simp [hX, bitsWord]
  omega

theorem dropMachine_deterministic : Deterministic dropMachine :=
  (dropTM ;; finish 1).deterministic_compile

/-! ## The reduction machine -/

section Red

variable (D : Machine)

/-- The reduction machine: count `n = |x|`, write `encodeNats [h, h] ++ true :: true :: x` with
`h = hOf d n`, and run `D` on it. -/
noncomputable def redTM (d : ℕ) : TM (D.tapes + 3 + 1) (Fin (D.symbols + 3)) :=
  countLen 0 (iP D) ;; emitOnes (iP D) (iB D) d ;; emitOnes (iP D) (iB D) d ;;
    writeR (iB D) (bit true) ;; writeR (iB D) (bit true) ;; rewind 0 ;; copyR 0 (iB D) (nb D) ;;
    erase 0 ;; rewind (iB D) ;; copyR (iB D) 0 (nb D) ;; rewind 0 ;;
    write (iM D) (mark D) ;; onTapes (σL D) (simTM D)

theorem redTM_deterministic (d : ℕ) : Deterministic (redTM D d).compile :=
  (redTM D d).deterministic_compile

variable {D}

/-- Tapes described by the four tapes in use (`0`, counter, output buffer, marker). -/
def St (a b c e : Machines.Tape (Fin (D.symbols + 3))) : Machines.Tapes (D.tapes + 4) (Fin (D.symbols + 3)) :=
  fun i => if i = 0 then a else if i = iP D then b else if i = iB D then c else
    if i = iM D then e else .ofWord [] []

section StLemmas

variable (a b c e a' : Machines.Tape (Fin (D.symbols + 3)))

@[simp] lemma St_zero : St a b c e 0 = a := by simp [St]
@[simp] lemma St_iP : St a b c e (iP D) = b := by simp [St, iP_ne_zero]
@[simp] lemma St_iB : St a b c e (iB D) = c := by simp [St, iB_ne_zero, iP_ne_iB.symm]
@[simp] lemma St_iM : St a b c e (iM D) = e := by
  simp [St, iM_ne_zero, iP_ne_iM.symm, iB_ne_iM.symm]

lemma St_other {i : Fin (D.tapes + 4)} (h0 : i ≠ 0) (hP : i ≠ iP D) (hB : i ≠ iB D)
    (hM : i ≠ iM D) : St a b c e i = .ofWord [] [] := by simp [St, h0, hP, hB, hM]

@[simp] lemma update_St_zero : update (St a b c e) 0 a' = St a' b c e := by
  funext i; by_cases h : i = 0
  · subst h; simp
  · simp [St, h]
@[simp] lemma update_St_iP : update (St a b c e) (iP D) a' = St a a' c e := by
  funext i; by_cases h : i = iP D
  · subst h; simp
  · simp [St, h]
@[simp] lemma update_St_iB : update (St a b c e) (iB D) a' = St a b a' e := by
  funext i; by_cases h : i = iB D
  · subst h; simp
  · simp [St, h]
@[simp] lemma update_St_iM : update (St a b c e) (iM D) a' = St a b c a' := by
  funext i; by_cases h : i = iM D
  · subst h; simp
  · simp [St, h]

end StLemmas

lemma inputTapes_eq_St (x : List Bool) :
    inputTapes (Γ := Fin (D.symbols + 3)) (D.tapes + 3) x =
      St (.ofWord [] (bitsWord x)) (.ofWord [] []) (.ofWord [] []) (.ofWord [] []) := by
  funext i
  by_cases h : i = 0
  · subst h; rw [inputTapes_zero]; simp
  · rw [inputTapes_ne_zero _ h]
    simp [St, h]

lemma length_natWord (n : ℕ) : (natWord n : List (Fin (D.symbols + 3))).length =
    (Nat.bits n).length := by simp [natWord]

/-- The word written by `redTM`. -/
def redInput (d : ℕ) (x : List Bool) : List Bool :=
  encodeNats [hOf d x.length, hOf d x.length] ++ true :: true :: x

lemma bitsWord_encodeNat_hOf {Γ : Type} [TapeAlphabet Γ] (d n : ℕ) :
    (bitsWord (encodeNat (hOf d n)) : List Γ) =
      List.replicate (2 * d * ((Nat.bits n).length + 1)) (bit true) ++ [bit false] := by
  rw [hOf, encodeNat_two_pow_sub_one]
  simp [bitsWord, List.map_replicate, Nat.mul_assoc]

lemma length_redInput (d : ℕ) (x : List Bool) :
    (redInput d x).length = 2 * (2 * d * ((Nat.bits x.length).length + 1) + 1) + x.length + 2 := by
  have e := congrArg List.length (bitsWord_encodeNat_hOf (Γ := Fin 3) d x.length)
  simp only [bitsWord, List.length_map, List.length_append, List.length_replicate,
    List.length_singleton] at e
  simp [redInput, encodeNats, e]
  ring

/-- **Specification of `redTM`.** -/
theorem redTM_runsWithin (d : ℕ) {x z : List Bool} {t : ℕ}
    (hD : ComputesWithin D (redInput d x) z t) :
    ∃ T', (redTM D d).RunsWithin (inputTapes (D.tapes + 3) x)
      (x.length * (4 * Nat.size x.length + 7) + 2 * (d * (5 * (Nat.bits x.length).length + 4) + 1)
        + 2 + (2 * x.length + 2) + 2 * x.length + (2 * x.length + 2)
        + 3 * (2 * (redInput d x).length + 2) + 1 + 2 * t) T' ∧
      T' 0 = Tape.ofWord [] (bitsWord z) := by
  set X : List (Fin (D.symbols + 3)) := bitsWord x with hX
  set U : List (Fin (D.symbols + 3)) := natWord x.length with hU
  set E : List (Fin (D.symbols + 3)) := bitsWord (encodeNat (hOf d x.length)) with hE
  set Y : List (Fin (D.symbols + 3)) := bitsWord (redInput d x) with hY
  set e₀ : Machines.Tape (Fin (D.symbols + 3)) := .ofWord [] [] with he₀
  have hXb : ∀ a ∈ X, a ≠ blank := fun a ha => bit_ne_blank_of_mem_bitsWord ha
  have hUb : ∀ a ∈ U, a ≠ blank := fun a ha => mem_natWord_ne_blank ha
  have hYb : ∀ a ∈ Y, a ≠ blank := fun a ha => bit_ne_blank_of_mem_bitsWord ha
  have hEeq : E = List.replicate (2 * d * (U.length + 1)) (bit true) ++ [bit false] := by
    rw [hE, bitsWord_encodeNat_hOf, hU, length_natWord]
  have hYeq : Y = E ++ E ++ [bit true, bit true] ++ X := by
    simp [hY, hE, hX, redInput, encodeNats, bitsWord]
  have hXl : X.length = x.length := by simp [hX, bitsWord]
  have hUl : U.length = (Nat.bits x.length).length := by rw [hU, length_natWord]
  -- 1. count
  have h1 := countLen_ofWord (iP_ne_zero (D := D)).symm X hXb [] 0 (St (.ofWord [] X) e₀ e₀ e₀)
    (by simp) (by simp [he₀, natWord])
  simp only [update_St_zero, update_St_iP, List.nil_append, zero_add] at h1
  rw [hXl] at h1
  -- 2., 3. the two codes of `h`
  have h2 := emitOnes_ofWord (iP_ne_iB (D := D)) U hUb d [] (St (.ofWord X []) (.ofWord [] U) e₀ e₀)
    (by simp [hU]) (by simp [he₀])
  rw [update_St_iB, List.nil_append, ← hEeq] at h2
  have h3 := emitOnes_ofWord (iP_ne_iB (D := D)) U hUb d E (St (.ofWord X []) (.ofWord [] U)
    (.ofWord E []) e₀) (by simp) (by simp)
  rw [update_St_iB, ← hEeq] at h3
  -- 4., 5. the padding
  have h4 := writeR_runsWithin (iB D) (bit true) (St (.ofWord X []) (.ofWord [] U)
    (.ofWord (E ++ E) []) e₀)
  simp only [St_iB, Tape.act_ofWord_right, List.tail_nil, update_St_iB] at h4
  have h5 := writeR_runsWithin (iB D) (bit true) (St (.ofWord X []) (.ofWord [] U)
    (.ofWord (E ++ E ++ [bit true]) []) e₀)
  simp only [St_iB, Tape.act_ofWord_right, List.tail_nil, update_St_iB] at h5
  -- 6. rewind the input
  have h6 := rewind_ofWord 0 (T := St (.ofWord X []) (.ofWord [] U)
    (.ofWord (E ++ E ++ [bit true] ++ [bit true]) []) e₀) (pre := X) (rest := []) (by simp) hXb
  simp only [update_St_zero, List.append_nil] at h6
  -- 7. copy the input
  have h7 := copyR_ofWord (iB_ne_zero (D := D)).symm (nb D) (pre := []) (u := X) (rest := [])
    (T := St (.ofWord [] X) (.ofWord [] U) (.ofWord (E ++ E ++ [bit true] ++ [bit true]) []) e₀)
    (dpre := E ++ E ++ [bit true] ++ [bit true]) (drest := []) (by simp)
    (fun a ha => by simpa [nb] using hXb a ha) (by simp [nb]) (by simp)
  simp only [update_St_zero, update_St_iB, List.nil_append, List.drop_nil] at h7
  rw [show E ++ E ++ [bit true] ++ [bit true] ++ X = Y by rw [hYeq]; simp] at h7
  -- 8. erase tape 0
  have h8 := erase_ofWord 0 (T := St (.ofWord X []) (.ofWord [] U) (.ofWord Y []) e₀)
    (pre := X) (rest := []) (by simp) (by simpa using hXb)
  simp only [update_St_zero] at h8
  -- 9. rewind the buffer
  have h9 := rewind_ofWord (iB D) (T := St (.ofWord [] []) (.ofWord [] U) (.ofWord Y []) e₀)
    (pre := Y) (rest := []) (by simp) hYb
  simp only [update_St_iB, List.append_nil] at h9
  -- 10. copy back
  have h10 := copyR_ofWord (iB_ne_zero (D := D)) (nb D) (pre := []) (u := Y) (rest := [])
    (T := St (.ofWord [] []) (.ofWord [] U) (.ofWord [] Y) e₀)
    (dpre := []) (drest := []) (by simp)
    (fun a ha => by simpa [nb] using hYb a ha) (by simp [nb]) (by simp)
  simp only [update_St_zero, update_St_iB, List.nil_append, List.drop_nil] at h10
  -- 11. rewind tape 0
  have h11 := rewind_ofWord 0 (T := St (.ofWord Y []) (.ofWord [] U) (.ofWord Y []) e₀)
    (pre := Y) (rest := []) (by simp) hYb
  simp only [update_St_zero, List.append_nil] at h11
  -- 12. the mark
  have h12 := write_runsWithin (iM D) (mark D) (St (.ofWord [] Y) (.ofWord [] U) (.ofWord Y []) e₀)
  simp only [St_iM, he₀, Tape.act_ofWord_stay, List.tail_nil, update_St_iM] at h12
  -- 13. simulate `D`
  set T12 := St (.ofWord [] Y) (.ofWord [] U) (.ofWord Y []) (.ofWord [] [mark D]) with hT12
  have hsim := simTM_runsWithin hD (T := T12 ∘ σL D)
    (fun j => by
      show T12 (σL D j.castSucc) = _
      rw [init_tape]
      by_cases hj : j = 0
      · subst hj
        rw [Fin.castSucc_zero, σL_zero, hT12, St_zero, inputTapes_zero]
        exact Tape.ext (by simp) (by simp [hY, bitsWord])
      · have h0 : σL D j.castSucc ≠ 0 := by
          intro h; apply hj; ext; have := congrArg Fin.val h; simpa [σL] using this
        rw [hT12, St_other _ _ _ _ h0 (σL_ne_iP _) (σL_ne_iB _) (σL_castSucc_ne_iM _),
          inputTapes_ne_zero _ hj]
        rfl)
    (by show T12 (σL D (mkI D)) = _; rw [σL_mkI, hT12, St_iM]; rfl)
  obtain ⟨T', h13', hT'0⟩ := hsim
  have h13 := onTapes_runsWithin (σL D) h13'
  have h := seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin
    (seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin
    (seq_runsWithin (seq_runsWithin h1 h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13
  rw [inputTapes_eq_St]
  refine ⟨_, h.mono ?_, by rw [← σL_zero, updateTapes_apply_self, hT'0]⟩
  have hYl : Y.length = (redInput d x).length := by simp [hY, bitsWord]
  rw [hUl] at *
  simp only [List.length_nil, List.append_nil, hYl, hXl]
  omega

end Red

end Lax119563Proofs.Hardness
