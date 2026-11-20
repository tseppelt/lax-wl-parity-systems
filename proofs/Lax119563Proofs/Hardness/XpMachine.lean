import Lax119563Proofs.Hardness.ExpMachine

/-!
# Padding the input and running a machine on it

For a deterministic machine `D`, the machine `(padTM D).compile` writes
`true :: true :: x` from its input `x` and runs `D` on it (by `simTM`). So if `D` computes `z`
from `true :: true :: x` within `t` steps, `padTM D` computes `z` from `x` within
`20 |x| + 41 + 2 t` steps (`padTM_computesWithin`). This removes the restriction to inputs of
length at least `2` of the composition of machines (`Main.Compose.compose_computesWithin`):
`D` is a composition, run on padded inputs.
-/

open Lax489179.TuringMachine (Machine Config Move Instruction init step run Deterministic)
open Lax119563.DeterministicTime Lax119563.BinaryEncodings

namespace Lax119563Proofs.Hardness

open Machines Machines.TM Function

section Pad

variable (D : Machine)

/-- The machine writing `true :: true :: x` and running `D` on it. -/
noncomputable def padTM : TM (D.tapes + 3 + 1) (Fin (D.symbols + 3)) :=
  writeR (iB D) (bit true) ;; writeR (iB D) (bit true) ;; copyR 0 (iB D) (nb D) ;;
    erase 0 ;; rewind (iB D) ;; copyR (iB D) 0 (nb D) ;; rewind 0 ;;
    write (iM D) (mark D) ;; onTapes (σL D) (simTM D)

theorem padTM_deterministic : Deterministic (padTM D).compile :=
  (padTM D).deterministic_compile

variable {D}

/-- **Specification of `padTM`.** -/
theorem padTM_runsWithin {x z : List Bool} {t : ℕ}
    (hD : ComputesWithin D (true :: true :: x) z t) :
    ∃ T', (padTM D).RunsWithin (inputTapes (D.tapes + 3) x) (20 * x.length + 40 + 2 * t) T' ∧
      T' 0 = Tape.ofWord [] (bitsWord z) := by
  set X : List (Fin (D.symbols + 3)) := bitsWord x with hX
  set Y : List (Fin (D.symbols + 3)) := bitsWord (true :: true :: x) with hY
  set e₀ : Machines.Tape (Fin (D.symbols + 3)) := .ofWord [] [] with he₀
  have hXb : ∀ a ∈ X, a ≠ blank := fun a ha => bit_ne_blank_of_mem_bitsWord ha
  have hYb : ∀ a ∈ Y, a ≠ blank := fun a ha => bit_ne_blank_of_mem_bitsWord ha
  have hYeq : Y = [bit true, bit true] ++ X := by simp [hY, hX, bitsWord]
  have hXl : X.length = x.length := by simp [hX, bitsWord]
  -- 1., 2. the padding
  have h1 := writeR_runsWithin (iB D) (bit true) (St (.ofWord [] X) e₀ e₀ e₀)
  simp only [St_iB, he₀, Tape.act_ofWord_right, List.tail_nil, update_St_iB,
    List.nil_append] at h1
  have h2 := writeR_runsWithin (iB D) (bit true) (St (.ofWord [] X) e₀
    (.ofWord [bit true] []) e₀)
  simp only [St_iB, Tape.act_ofWord_right, List.tail_nil, update_St_iB,
    List.singleton_append] at h2
  -- 3. copy the input
  have h3 := copyR_ofWord (iB_ne_zero (D := D)).symm (nb D) (pre := []) (u := X) (rest := [])
    (T := St (.ofWord [] X) e₀ (.ofWord [bit true, bit true] []) e₀)
    (dpre := [bit true, bit true]) (drest := []) (by simp)
    (fun a ha => by simpa [nb] using hXb a ha) (by simp [nb]) (by simp)
  simp only [update_St_zero, update_St_iB, List.nil_append, List.drop_nil] at h3
  rw [show [bit true, bit true] ++ X = Y by rw [hYeq]] at h3
  -- 4. erase tape 0
  have h4 := erase_ofWord 0 (T := St (.ofWord X []) e₀ (.ofWord Y []) e₀)
    (pre := X) (rest := []) (by simp) (by simpa using hXb)
  simp only [update_St_zero] at h4
  -- 5. rewind the buffer
  have h5 := rewind_ofWord (iB D) (T := St (.ofWord [] []) e₀ (.ofWord Y []) e₀)
    (pre := Y) (rest := []) (by simp) hYb
  simp only [update_St_iB, List.append_nil] at h5
  -- 6. copy back
  have h6 := copyR_ofWord (iB_ne_zero (D := D)) (nb D) (pre := []) (u := Y) (rest := [])
    (T := St (.ofWord [] []) e₀ (.ofWord [] Y) e₀)
    (dpre := []) (drest := []) (by simp)
    (fun a ha => by simpa [nb] using hYb a ha) (by simp [nb]) (by simp)
  simp only [update_St_zero, update_St_iB, List.nil_append, List.drop_nil] at h6
  -- 7. rewind tape 0
  have h7 := rewind_ofWord 0 (T := St (.ofWord Y []) e₀ (.ofWord Y []) e₀)
    (pre := Y) (rest := []) (by simp) hYb
  simp only [update_St_zero, List.append_nil] at h7
  -- 8. the mark
  have h8 := write_runsWithin (iM D) (mark D) (St (.ofWord [] Y) e₀ (.ofWord Y []) e₀)
  simp only [St_iM, he₀, Tape.act_ofWord_stay, List.tail_nil, update_St_iM] at h8
  -- 9. simulate `D`
  set T8 := St (.ofWord [] Y) e₀ (.ofWord Y []) (.ofWord [] [mark D]) with hT8
  have hsim := simTM_runsWithin hD (T := T8 ∘ σL D)
    (fun j => by
      show T8 (σL D j.castSucc) = _
      rw [init_tape]
      by_cases hj : j = 0
      · subst hj
        rw [Fin.castSucc_zero, σL_zero, hT8, St_zero, inputTapes_zero]
        exact Tape.ext (by simp) (by simp [hY, bitsWord])
      · have h0 : σL D j.castSucc ≠ 0 := by
          intro h; apply hj; ext; have := congrArg Fin.val h; simpa [σL] using this
        rw [hT8, St_other _ _ _ _ h0 (σL_ne_iP _) (σL_ne_iB _) (σL_castSucc_ne_iM _),
          inputTapes_ne_zero _ hj]
        rfl)
    (by show T8 (σL D (mkI D)) = _; rw [σL_mkI, hT8, St_iM]; rfl)
  obtain ⟨T', h9', hT'0⟩ := hsim
  have h9 := onTapes_runsWithin (σL D) h9'
  have h := seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin
    (seq_runsWithin (seq_runsWithin (seq_runsWithin h1 h2) h3) h4) h5) h6) h7) h8) h9
  rw [inputTapes_eq_St]
  refine ⟨_, h.mono ?_, by rw [← σL_zero, updateTapes_apply_self, hT'0]⟩
  have hYl : Y.length = x.length + 2 := by simp [hY, bitsWord]
  simp only [List.length_nil, List.append_nil, hYl, hXl]
  omega

/-- **Padding and running.** -/
theorem padTM_computesWithin {x z : List Bool} {t : ℕ}
    (hD : ComputesWithin D (true :: true :: x) z t) :
    ComputesWithin (padTM D).compile x z (20 * x.length + 41 + 2 * t) := by
  obtain ⟨T', hrun, hT'⟩ := padTM_runsWithin hD
  have hcw := (padTM D).computesWithin (fun _ _ => false) hrun (y := z)
    (by rw [hT']; simp [Machines.bitsWord])
  exact Main.Compose.computesWithin_mono' hcw (by omega)

end Pad

end Lax119563Proofs.Hardness
