import Lax119563Proofs.Hardness.LeadMachine

/-!
# Keeping the input behind the output

For a deterministic machine `D`, the machine `(withSuffix D).compile` copies its input `x` to
a separate tape, runs `D` on `x` (by `simTM`), and then appends `x` to the output of `D`. So
if `D` computes `z` from `x` within `t` steps, it computes `z ++ x` within
`16 (t + |x| + |z| + 1)` steps (`withSuffix_computesWithin`).
-/

open Lax489179.TuringMachine (Machine Config Move Instruction init step run Deterministic)
open Lax119563.DeterministicTime Lax119563.BinaryEncodings

namespace Lax119563Proofs.Hardness

open Machines Machines.TM Function

variable (D : Machine)

/-- The machine appending the input to the output of `D`. -/
noncomputable def withSuffix : TM (D.tapes + 3 + 1) (Fin (D.symbols + 3)) :=
  copyR 0 (iP D) (nb D) ;; rewind 0 ;; rewind (iP D) ;; write (iM D) (mark D) ;;
    onTapes (σL D) (simTM D) ;; scanR 0 (nb D) ;; copyR (iP D) 0 (nb D)

variable {D}

/-- **Specification of `withSuffix`** on structured tapes. -/
theorem withSuffix_runsWithin {x z : List Bool} {t : ℕ} (hD : ComputesWithin D x z t) :
    ∃ T', (withSuffix D).RunsWithin (inputTapes (D.tapes + 3) x)
      (2 * t + 8 * x.length + 2 * z.length + 6) T' ∧
      T' 0 = Tape.ofWord (bitsWord (z ++ x)) [] := by
  set X : List (Fin (D.symbols + 3)) := bitsWord x with hX
  set Z : List (Fin (D.symbols + 3)) := bitsWord z with hZ
  set T0 := inputTapes (Γ := Fin (D.symbols + 3)) (D.tapes + 3) x with hT0
  have hT00 : T0 0 = .ofWord [] (X ++ []) := by
    rw [hT0, inputTapes_zero]; simp [hX, bitsWord]
  have hT0x : ∀ y : Fin (D.tapes + 4), y ≠ 0 → T0 y = .ofWord [] [] :=
    fun y hy => inputTapes_ne_zero _ hy
  -- 1. copy the input
  obtain ⟨T1, h1, f1a, f1b, f1c⟩ : ∃ T1, (copyR 0 (iP D) (nb D)).RunsWithin T0
      (2 * X.length) T1 ∧ T1 0 = .ofWord X [] ∧ T1 (iP D) = .ofWord X [] ∧
      ∀ y, y ≠ 0 → y ≠ iP D → T1 y = T0 y :=
    ⟨_, copyR_ofWord (iP_ne_zero (D := D)).symm (nb D) (pre := []) (u := X) (rest := [])
      (dpre := []) (drest := []) hT00 (nb_bitsWord _) (by simp [nb]) (hT0x _ iP_ne_zero),
      by simp [update_of_ne (iP_ne_zero (D := D)).symm],
      by simp,
      fun y h0 hP => by simp [update_of_ne h0, update_of_ne hP]⟩
  -- 2. rewind tape 0
  obtain ⟨T2, h2, f2a, f2c⟩ : ∃ T2, (rewind 0).RunsWithin T1 (2 * X.length + 2) T2 ∧
      T2 0 = .ofWord [] X ∧ ∀ y, y ≠ 0 → T2 y = T1 y :=
    ⟨_, rewind_ofWord 0 f1a (ne_blank_bitsWord _), by simp,
      fun y h0 => by simp [update_of_ne h0]⟩
  -- 3. rewind the copy
  obtain ⟨T3, h3, f3a, f3b, f3c⟩ : ∃ T3, (rewind (iP D)).RunsWithin T2 (2 * X.length + 2) T3 ∧
      T3 0 = .ofWord [] X ∧ T3 (iP D) = .ofWord [] X ∧
      ∀ y, y ≠ 0 → y ≠ iP D → T3 y = T0 y :=
    ⟨_, rewind_ofWord (iP D) (by rw [f2c _ iP_ne_zero, f1b]) (ne_blank_bitsWord _),
      by simp [update_of_ne (iP_ne_zero (D := D)).symm, f2a], by simp,
      fun y h0 hP => by simp [update_of_ne hP, f2c _ h0, f1c _ h0 hP]⟩
  -- 4. mark the origin
  obtain ⟨T4, h4, f4a, f4b, f4m, f4c⟩ : ∃ T4, (write (iM D) (mark D)).RunsWithin T3 1 T4 ∧
      T4 0 = .ofWord [] X ∧ T4 (iP D) = .ofWord [] X ∧ T4 (iM D) = .ofWord [] [mark D] ∧
      ∀ y, y ≠ 0 → y ≠ iP D → y ≠ iM D → T4 y = T0 y :=
    ⟨_, write_runsWithin _ _ _, by simp [update_of_ne (iM_ne_zero (D := D)).symm, f3a],
      by simp [update_of_ne (iP_ne_iM (D := D)), f3b],
      by simp [f3c _ iM_ne_zero iP_ne_iM.symm, hT0x _ iM_ne_zero, Tape.act_ofWord_stay],
      fun y h0 hP hM => by simp [update_of_ne hM, f3c _ h0 hP]⟩
  -- 5. simulate `D`
  have hsim := simTM_runsWithin hD (T := T4 ∘ σL D)
    (fun j => by
      show T4 (σL D j.castSucc) = _
      rw [init_tape]
      by_cases hj : j = 0
      · subst hj
        rw [Fin.castSucc_zero, σL_zero, f4a, inputTapes_zero]
        exact Tape.ext (by simp) (by simp [hX, bitsWord])
      · have h0 : σL D j.castSucc ≠ 0 := by
          intro h; apply hj; ext; have := congrArg Fin.val h; simpa [σL] using this
        rw [f4c _ h0 (σL_ne_iP _) (σL_castSucc_ne_iM _), hT0x _ h0, inputTapes_ne_zero _ hj]
        rfl)
    (by show T4 (σL D (mkI D)) = _; rw [σL_mkI, f4m]; rfl)
  obtain ⟨T', h5', hT'0⟩ := hsim
  have h5 := onTapes_runsWithin (σL D) h5'
  obtain ⟨T5, h5, f5a, f5b⟩ : ∃ T5, (onTapes (σL D) (simTM D)).RunsWithin T4 (2 * t) T5 ∧
      T5 0 = .ofWord [] Z ∧ T5 (iP D) = .ofWord [] X :=
    ⟨_, h5, by rw [← σL_zero, updateTapes_apply_self, hT'0],
      by rw [updateTapes_apply_of_not_mem _ _ _ σL_ne_iP, f4b]⟩
  -- 6. move to the end of the output
  obtain ⟨T6, h6, f6a, f6b⟩ : ∃ T6, (scanR 0 (nb D)).RunsWithin T5 (2 * Z.length) T6 ∧
      T6 0 = .ofWord Z [] ∧ T6 (iP D) = .ofWord [] X :=
    ⟨_, scanR_ofWord 0 (nb D) (pre := []) (u := Z) (rest := []) (by simpa using f5a)
      (nb_bitsWord _) (by simp [nb]), by simp,
      by simp [update_of_ne (iP_ne_zero (D := D)), f5b]⟩
  -- 8. append the input
  obtain ⟨T8, h8, f8a⟩ : ∃ T8, (copyR (iP D) 0 (nb D)).RunsWithin T6 (2 * X.length) T8 ∧
      T8 0 = .ofWord (Z ++ X) [] :=
    ⟨_, copyR_ofWord (iP_ne_zero (D := D)) (nb D) (pre := []) (u := X) (rest := [])
      (dpre := Z) (drest := []) (by simpa using f6b) (nb_bitsWord _) (by simp [nb]) f6a,
      by simp⟩
  have h := seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin
    (seq_runsWithin h1 h2) h3) h4) h5) h6) h8
  refine ⟨T8, h.mono ?_, by rw [f8a]; simp [hX, hZ, bitsWord]⟩
  have hXl : X.length = x.length := by simp [hX, bitsWord]
  have hZl : Z.length = z.length := by simp [hZ, bitsWord]
  omega

/-- **Keeping the input behind the output.** -/
theorem withSuffix_computesWithin {x z : List Bool} {t : ℕ} (hD : ComputesWithin D x z t) :
    ComputesWithin (withSuffix D).compile x (z ++ x) (16 * (t + x.length + 1)) := by
  obtain ⟨T', h, hT'⟩ := withSuffix_runsWithin hD
  have hc := (withSuffix D).computesWithin (fun _ _ => false) h
    (y := z ++ x) (by rw [hT']; simp [bitsWord])
  have hz := length_le_of_computesWithin hD
  refine Main.Compose.computesWithin_mono' hc ?_
  omega

theorem withSuffix_deterministic : Deterministic (withSuffix D).compile :=
  (withSuffix D).deterministic_compile

end Lax119563Proofs.Hardness
