import Lax119563Proofs.Hardness.SimMachine
import Lax119563Proofs.Machines.ComposeComputes

/-!
# Keeping the leading number of the input

For a deterministic machine `D`, the machine `(withLead D).compile` copies the leading number
code `encodeNat m` of its input to a separate tape, runs `D` on the whole input (by `simTM`),
and then writes `encodeNat m` in front of the output of `D`. So if `D` computes `z` from
`encodeNat m ++ v` within `t` steps, it computes `encodeNat m ++ z` within
`16 (t + |encodeNat m ++ v| + 1)` steps (`withLead_computesWithin`).
-/

open Lax489179.TuringMachine (Machine Config Move Instruction init step run Deterministic)
open Lax119563.DeterministicTime Lax119563.BinaryEncodings

namespace Lax119563Proofs.Hardness

open Machines Machines.TM Function

section CopyLead

variable {Γ : Type} [TapeAlphabet Γ] {k : ℕ}

/-- Copy one symbol from tape `i` to tape `j`, moving both heads right. -/
def cp (i j : Fin k) : TM k Γ := act₂ i j fun a _ => ((a, .right), (a, .right))

/-- Copy the leading number code from tape `i` to tape `j`. -/
def copyLead [DecidableEq Γ] (i j : Fin k) : TM k Γ :=
  loop (fun s => decide (s i = bit true)) (cp i j ;; cp i j) ;; cp i j

/-- The pairs `true, d` of a number code. -/
def pairs (ds : List Bool) : List Bool := ds.flatMap fun d => [true, d]

lemma cp_ofWord {i j : Fin k} (hij : i ≠ j) {T : Tapes k Γ} {pre rest dpre : List Γ} (a : Γ)
    (hTi : T i = .ofWord pre (a :: rest)) (hTj : T j = .ofWord dpre []) :
    (cp i j).RunsWithin T 1
      (update (update T i (.ofWord (pre ++ [a]) rest)) j (.ofWord (dpre ++ [a]) [])) := by
  have h₁ := act₂_runsWithin hij (fun a _ => ((a, Move.right), (a, Move.right))) T
  simp only [hTi, hTj, Tape.read_ofWord_cons, Tape.act_ofWord_right, List.tail_cons,
    List.tail_nil] at h₁
  exact h₁

theorem copyLoop_ofWord [DecidableEq Γ] {i j : Fin k} (hij : i ≠ j) (ds : List Bool) :
    ∀ {T : Tapes k Γ} {pre dpre r : List Γ},
    T i = .ofWord pre (bitsWord (pairs ds) ++ (bit false :: r)) → T j = .ofWord dpre [] →
    (loop (fun s => decide (s i = bit true)) (cp i j ;; cp i j)).RunsWithin T (3 * ds.length)
      (update (update T i (.ofWord (pre ++ bitsWord (pairs ds)) (bit false :: r))) j
        (.ofWord (dpre ++ bitsWord (pairs ds)) [])) := by
  induction ds with
  | nil =>
    intro T pre dpre r hTi hTj
    have hc : (fun s : Fin k → Γ => decide (s i = bit true)) (readAll T) = false := by
      simp [readAll, hTi, pairs, bitsWord]
    refine (loop_runsWithin_exit hc).congr_right ?_
    simp only [pairs, List.flatMap_nil, bitsWord, List.map_nil, List.append_nil,
      List.nil_append] at hTi ⊢
    rw [← hTi, ← hTj]; simp
  | cons d ds ih =>
    intro T pre dpre r hTi hTj
    have hTi' : T i = .ofWord pre (bit true :: bit d :: (bitsWord (pairs ds) ++ bit false :: r)) := by
      rw [hTi]; simp [pairs, bitsWord]
    have h₁ := cp_ofWord hij (bit true) hTi' hTj
    set T₁ := update (update T i (Tape.ofWord (pre ++ [bit true])
      (bit d :: (bitsWord (pairs ds) ++ bit false :: r)))) j (Tape.ofWord (dpre ++ [bit true]) [])
    have h₂ := cp_ofWord (T := T₁) (pre := pre ++ [bit true])
      (rest := bitsWord (pairs ds) ++ bit false :: r) (dpre := dpre ++ [bit true]) hij (bit d) (by simp [T₁, update_of_ne hij]) (by simp [T₁])
    have h₃ := ih (T := update (update T₁ i (Tape.ofWord (pre ++ [bit true] ++ [bit d])
        (bitsWord (pairs ds) ++ bit false :: r))) j (Tape.ofWord (dpre ++ [bit true] ++ [bit d]) []))
      (pre := pre ++ [bit true] ++ [bit d]) (dpre := dpre ++ [bit true] ++ [bit d]) (r := r)
      (by simp [update_of_ne hij]) (by simp)
    have hc : (fun s : Fin k → Γ => decide (s i = bit true)) (readAll T) = true := by
      simp [readAll, hTi']
    have h := loop_runsWithin_iter hc (seq_runsWithin h₁ h₂) h₃
    refine (h.mono (by simp; omega)).congr_right ?_
    simp only [T₁, update_update_update_update hij]
    congr 2 <;> simp [pairs, bitsWord]

theorem copyLead_ofWord [DecidableEq Γ] {i j : Fin k} (hij : i ≠ j) (m : ℕ) {T : Tapes k Γ}
    {pre dpre r : List Γ} (hTi : T i = .ofWord pre (bitsWord (encodeNat m) ++ r))
    (hTj : T j = .ofWord dpre []) :
    (copyLead i j).RunsWithin T (3 * (Nat.bits m).length + 1)
      (update (update T i (.ofWord (pre ++ bitsWord (encodeNat m)) r)) j
        (.ofWord (dpre ++ bitsWord (encodeNat m)) [])) := by
  have he : bitsWord (encodeNat m) = (bitsWord (pairs (Nat.bits m)) ++ [bit false] : List Γ) := by
    simp [encodeNat, pairs, bitsWord]
  have h₁ := copyLoop_ofWord hij (Nat.bits m) (T := T) (pre := pre) (dpre := dpre) (r := r)
    (by rw [hTi, he]; simp) hTj
  have h₂ := cp_ofWord (T := update (update T i (.ofWord (pre ++ bitsWord (pairs (Nat.bits m)))
      (bit false :: r))) j (.ofWord (dpre ++ bitsWord (pairs (Nat.bits m))) []))
      (pre := pre ++ bitsWord (pairs (Nat.bits m))) (rest := r)
      (dpre := dpre ++ bitsWord (pairs (Nat.bits m))) hij (bit false)
    (by simp [update_of_ne hij]) (by simp)
  refine (seq_runsWithin h₁ h₂).congr_right ?_
  simp only [update_update_update_update hij, he]
  congr 2 <;> simp

end CopyLead

/-! ## The machine -/

variable (D : Machine)

/-- The embedding of the tapes of `simTM D`. -/
def σL : Fin (D.tapes + 2) ↪ Fin (D.tapes + 4) := Fin.castLEEmb (by omega)

/-- The tape holding the leading code. -/
def iP : Fin (D.tapes + 4) := ⟨D.tapes + 2, by omega⟩
/-- The buffer tape. -/
def iB : Fin (D.tapes + 4) := ⟨D.tapes + 3, by omega⟩
/-- The marker tape. -/
def iM : Fin (D.tapes + 4) := ⟨D.tapes + 1, by omega⟩

/-- Non-blank symbols. -/
def nb (a : Fin (D.symbols + 3)) : Bool := decide (a ≠ blank)

/-- The machine keeping the leading number of the input in front of the output of `D`. -/
noncomputable def withLead : TM (D.tapes + 3 + 1) (Fin (D.symbols + 3)) :=
  copyLead 0 (iP D) ;; rewind 0 ;; rewind (iP D) ;; write (iM D) (mark D) ;;
    onTapes (σL D) (simTM D) ;; copyR 0 (iB D) (nb D) ;; erase 0 ;; copyR (iP D) 0 (nb D) ;;
    rewind (iB D) ;; copyR (iB D) 0 (nb D)

variable {D}

lemma init_tape (y : List Bool) (j : Fin (D.tapes + 1)) :
    (init D y).tape j = ((inputTapes (Γ := Fin (D.symbols + 3)) D.tapes y) j).cells := by
  funext z
  simp only [init, inputTapes]
  by_cases hj : j = 0
  · subst hj
    simp only [true_and, if_true, listCells, List.getElem?_map]
    by_cases hz : 0 ≤ z
    · rw [if_pos hz, if_pos hz]
      rcases y[z.toNat]? with _ | b
      · rfl
      · cases b <;> rfl
    · rw [if_neg hz, if_neg hz]; rfl
  · rw [if_neg (fun h => hj h.1), if_neg hj]; rfl

/-- **Specification of `simTM`.** -/
theorem simTM_runsWithin {y z : List Bool} {t : ℕ} (hD : ComputesWithin D y z t)
    {T : Machines.Tapes (D.tapes + 2) (Fin (D.symbols + 3))}
    (hT : ∀ j : Fin (D.tapes + 1), T j.castSucc = ⟨0, (init D y).tape j⟩)
    (hmk : T (mkI D) = ⟨0, markCells D⟩) :
    ∃ T', (simTM D).RunsWithin T (2 * t) T' ∧ T' 0 = Tape.ofWord [] (bitsWord z) := by
  have hR : Rel (init D y) true T :=
    ⟨fun j => hT j, hmk, fun _ => rfl, fun h => by simp [init] at h⟩
  obtain ⟨t', ht', T', hH, hT'⟩ := sim_haltsFrom t (init D y) true T rfl hR hD.1
  have hh := Main.Compose.head_natAbs_le D y 0 t
  refine ⟨T', ⟨t', by unfold runOn at hh; omega, hH⟩, ?_⟩
  have e : (runOn D y t).tape 0 = (Tape.ofWord [] (bitsWord z) : Tape (Fin (D.symbols + 3))).cells := by
    rw [hD.2, init_tape, inputTapes_zero]
  rw [hT']
  exact Tape.ext (by simp) e

section Indices

lemma iP_ne_zero : iP D ≠ 0 := by simp [iP, Fin.ext_iff]
lemma iB_ne_zero : iB D ≠ 0 := by simp [iB, Fin.ext_iff]
lemma iM_ne_zero : iM D ≠ 0 := by simp [iM, Fin.ext_iff]
lemma iP_ne_iB : iP D ≠ iB D := by simp [iP, iB, Fin.ext_iff]
lemma iP_ne_iM : iP D ≠ iM D := by simp [iP, iM, Fin.ext_iff]
lemma iB_ne_iM : iB D ≠ iM D := by simp [iB, iM, Fin.ext_iff]
lemma σL_ne_iP (i : Fin (D.tapes + 2)) : σL D i ≠ iP D := by
  simp [σL, iP, Fin.ext_iff]; omega
lemma σL_ne_iB (i : Fin (D.tapes + 2)) : σL D i ≠ iB D := by
  simp [σL, iB, Fin.ext_iff]; omega
lemma σL_zero : σL D 0 = 0 := by simp [σL]
lemma σL_mkI : σL D (mkI D) = iM D := by simp [σL, mkI, iM, Fin.ext_iff]
lemma σL_castSucc_ne_iM (j : Fin (D.tapes + 1)) : σL D j.castSucc ≠ iM D := by
  simp [σL, iM, Fin.ext_iff]; omega

end Indices

lemma nb_bitsWord (l : List Bool) : ∀ a ∈ (bitsWord l : List (Fin (D.symbols + 3))), nb D a = true :=
  fun _ ha => by simpa [nb] using bit_ne_blank_of_mem_bitsWord ha

lemma ne_blank_bitsWord (l : List Bool) : ∀ a ∈ (bitsWord l : List (Fin (D.symbols + 3))), a ≠ blank :=
  fun _ ha => bit_ne_blank_of_mem_bitsWord ha

/-- **Specification of `withLead`** on structured tapes. -/
theorem withLead_runsWithin {m : ℕ} {v z : List Bool} {t : ℕ}
    (hD : ComputesWithin D (encodeNat m ++ v) z t) :
    ∃ T', (withLead D).RunsWithin (inputTapes (D.tapes + 3) (encodeNat m ++ v))
      (2 * t + 8 * (encodeNat m).length + 8 * z.length + 10) T' ∧
      T' 0 = Tape.ofWord (bitsWord (encodeNat m ++ z)) [] := by
  set p : List (Fin (D.symbols + 3)) := bitsWord (encodeNat m) with hp
  set V : List (Fin (D.symbols + 3)) := bitsWord v with hV
  set Z : List (Fin (D.symbols + 3)) := bitsWord z with hZ
  set T0 := inputTapes (Γ := Fin (D.symbols + 3)) (D.tapes + 3) (encodeNat m ++ v) with hT0
  have hT00 : T0 0 = .ofWord [] (p ++ V) := by
    rw [hT0, inputTapes_zero]; simp [hp, hV, bitsWord]
  have hT0x : ∀ x : Fin (D.tapes + 4), x ≠ 0 → T0 x = .ofWord [] [] :=
    fun x hx => inputTapes_ne_zero _ hx
  -- 1. copy the leading code
  obtain ⟨T1, h1, f1a, f1b, f1c⟩ : ∃ T1, (copyLead 0 (iP D)).RunsWithin T0
      (3 * (Nat.bits m).length + 1) T1 ∧ T1 0 = .ofWord p V ∧ T1 (iP D) = .ofWord p [] ∧
      ∀ x, x ≠ 0 → x ≠ iP D → T1 x = T0 x :=
    ⟨_, copyLead_ofWord (iP_ne_zero (D := D)).symm m (pre := []) (dpre := []) (r := V) hT00
      (hT0x _ iP_ne_zero), by simp [update_of_ne (iP_ne_zero (D := D)).symm, hp],
      by simp [hp], fun x h0 hP => by simp [update_of_ne h0, update_of_ne hP]⟩
  -- 2. rewind tape 0
  obtain ⟨T2, h2, f2a, f2c⟩ : ∃ T2, (rewind 0).RunsWithin T1 (2 * p.length + 2) T2 ∧
      T2 0 = .ofWord [] (p ++ V) ∧ ∀ x, x ≠ 0 → T2 x = T1 x :=
    ⟨_, rewind_ofWord 0 f1a (ne_blank_bitsWord _), by simp,
      fun x h0 => by simp [update_of_ne h0]⟩
  -- 3. rewind the code tape
  obtain ⟨T3, h3, f3a, f3b, f3c⟩ : ∃ T3, (rewind (iP D)).RunsWithin T2 (2 * p.length + 2) T3 ∧
      T3 0 = .ofWord [] (p ++ V) ∧ T3 (iP D) = .ofWord [] p ∧
      ∀ x, x ≠ 0 → x ≠ iP D → T3 x = T0 x :=
    ⟨_, rewind_ofWord (iP D) (by rw [f2c _ iP_ne_zero, f1b]) (ne_blank_bitsWord _),
      by simp [update_of_ne (iP_ne_zero (D := D)).symm, f2a], by simp,
      fun x h0 hP => by simp [update_of_ne hP, f2c _ h0, f1c _ h0 hP]⟩
  -- 4. mark the origin
  obtain ⟨T4, h4, f4a, f4b, f4m, f4c⟩ : ∃ T4, (write (iM D) (mark D)).RunsWithin T3 1 T4 ∧
      T4 0 = .ofWord [] (p ++ V) ∧ T4 (iP D) = .ofWord [] p ∧ T4 (iM D) = .ofWord [] [mark D] ∧
      ∀ x, x ≠ 0 → x ≠ iP D → x ≠ iM D → T4 x = T0 x :=
    ⟨_, write_runsWithin _ _ _, by simp [update_of_ne (iM_ne_zero (D := D)).symm, f3a],
      by simp [update_of_ne (iP_ne_iM (D := D)), f3b],
      by simp [f3c _ iM_ne_zero iP_ne_iM.symm, hT0x _ iM_ne_zero, Tape.act_ofWord_stay],
      fun x h0 hP hM => by simp [update_of_ne hM, f3c _ h0 hP]⟩
  -- 5. simulate `D`
  have hsim := simTM_runsWithin hD (T := T4 ∘ σL D)
    (fun j => by
      show T4 (σL D j.castSucc) = _
      rw [init_tape]
      by_cases hj : j = 0
      · subst hj
        rw [Fin.castSucc_zero, σL_zero, f4a, inputTapes_zero]
        exact Tape.ext (by simp) (by simp [hp, hV, bitsWord])
      · have h0 : σL D j.castSucc ≠ 0 := by
          intro h; apply hj; ext; have := congrArg Fin.val h; simpa [σL] using this
        rw [f4c _ h0 (σL_ne_iP _) (σL_castSucc_ne_iM _), hT0x _ h0, inputTapes_ne_zero _ hj]
        rfl)
    (by show T4 (σL D (mkI D)) = _; rw [σL_mkI, f4m]; rfl)
  obtain ⟨T', h5', hT'0⟩ := hsim
  have h5 := onTapes_runsWithin (σL D) h5'
  obtain ⟨T5, h5, f5a, f5b, f5B⟩ : ∃ T5, (onTapes (σL D) (simTM D)).RunsWithin T4 (2 * t) T5 ∧
      T5 0 = .ofWord [] Z ∧ T5 (iP D) = .ofWord [] p ∧ T5 (iB D) = .ofWord [] [] :=
    ⟨_, h5, by rw [← σL_zero, updateTapes_apply_self, hT'0],
      by rw [updateTapes_apply_of_not_mem _ _ _ σL_ne_iP, f4b],
      by rw [updateTapes_apply_of_not_mem _ _ _ σL_ne_iB, f4c _ iB_ne_zero iP_ne_iB.symm
        iB_ne_iM, hT0x _ iB_ne_zero]⟩
  -- 6. copy the output to the buffer
  obtain ⟨T6, h6, f6a, f6b, f6B⟩ : ∃ T6, (copyR 0 (iB D) (nb D)).RunsWithin T5 (2 * Z.length) T6 ∧
      T6 0 = .ofWord Z [] ∧ T6 (iP D) = .ofWord [] p ∧ T6 (iB D) = .ofWord Z [] :=
    ⟨_, copyR_ofWord (iB_ne_zero (D := D)).symm (nb D) (pre := []) (u := Z) (rest := [])
      (by simpa using f5a) (nb_bitsWord _) (by simp [nb]) f5B,
      by simp [update_of_ne (iB_ne_zero (D := D)).symm],
      by simp [update_of_ne (iP_ne_iB (D := D)), update_of_ne (iP_ne_zero (D := D)), f5b],
      by simp⟩
  -- 7. erase tape 0
  obtain ⟨T7, h7, f7a, f7b, f7B⟩ : ∃ T7, (erase 0).RunsWithin T6 (2 * Z.length + 2) T7 ∧
      T7 0 = .ofWord [] [] ∧ T7 (iP D) = .ofWord [] p ∧ T7 (iB D) = .ofWord Z [] := by
    refine ⟨_, (erase_ofWord 0 f6a (by simpa using ne_blank_bitsWord z)).mono (by simp), by simp,
      by simp [update_of_ne (iP_ne_zero (D := D)), f6b],
      by simp [update_of_ne (iB_ne_zero (D := D)), f6B]⟩
  -- 8. write the leading code on tape 0
  obtain ⟨T8, h8, f8a, f8B⟩ : ∃ T8, (copyR (iP D) 0 (nb D)).RunsWithin T7 (2 * p.length) T8 ∧
      T8 0 = .ofWord p [] ∧ T8 (iB D) = .ofWord Z [] :=
    ⟨_, copyR_ofWord (iP_ne_zero (D := D)) (nb D) (pre := []) (u := p) (rest := [])
      (by simpa using f7b) (nb_bitsWord _) (by simp [nb]) f7a, by simp,
      by simp [update_of_ne (iB_ne_zero (D := D)), update_of_ne (iP_ne_iB (D := D)).symm, f7B]⟩
  -- 9. rewind the buffer
  obtain ⟨T9, h9, f9a, f9B⟩ : ∃ T9, (rewind (iB D)).RunsWithin T8 (2 * Z.length + 2) T9 ∧
      T9 0 = .ofWord p [] ∧ T9 (iB D) = .ofWord [] Z :=
    ⟨_, rewind_ofWord (iB D) f8B (ne_blank_bitsWord _),
      by simp [update_of_ne (iB_ne_zero (D := D)).symm, f8a], by simp⟩
  -- 10. append the output
  obtain ⟨T10, h10, f10a⟩ : ∃ T10, (copyR (iB D) 0 (nb D)).RunsWithin T9 (2 * Z.length) T10 ∧
      T10 0 = .ofWord (p ++ Z) [] :=
    ⟨_, copyR_ofWord (iB_ne_zero (D := D)) (nb D) (pre := []) (u := Z) (rest := [])
      (by simpa using f9B) (nb_bitsWord _) (by simp [nb]) f9a, by simp⟩
  have h := seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin
    (seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin h1 h2) h3) h4) h5) h6) h7)
    h8) h9) h10
  refine ⟨T10, h.mono ?_, by rw [f10a]; simp [hp, hZ, bitsWord]⟩
  have hpl : p.length = (encodeNat m).length := by simp [hp, bitsWord]
  have hZl : Z.length = z.length := by simp [hZ, bitsWord]
  have hb : 2 * (Nat.bits m).length + 1 = (encodeNat m).length := by simp [encodeNat]; omega
  omega

/-- **Keeping the leading number.** -/
theorem withLead_computesWithin {m : ℕ} {v z : List Bool} {t : ℕ}
    (hD : ComputesWithin D (encodeNat m ++ v) z t) :
    ComputesWithin (withLead D).compile (encodeNat m ++ v) (encodeNat m ++ z)
      (16 * (t + (encodeNat m ++ v).length + 1)) := by
  obtain ⟨T', h, hT'⟩ := withLead_runsWithin hD
  have hc := (withLead D).computesWithin (fun _ _ => false) h
    (y := encodeNat m ++ z) (by rw [hT']; simp [bitsWord])
  have hz := length_le_of_computesWithin hD
  refine Main.Compose.computesWithin_mono' hc ?_
  simp only [List.length_append] at hz ⊢
  omega

end Lax119563Proofs.Hardness
