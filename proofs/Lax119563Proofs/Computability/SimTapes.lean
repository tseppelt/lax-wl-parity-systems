import Lax119563Proofs.Computability.SimDefs

/-!
# Simulating a machine: tapes as pairs of stacks

`RepT c j L R`: the stacks `L` and `R` represent tape `j` of the configuration `c` (cells left
of the head nearest first, and cells from the head on; missing entries are blank). The
effect of the per-tape statements (`popT`, `pushT`, `opT`) and of their sequences over all
tapes (`exec_seqL_tapes`, `good_seqL`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax489179.TuringMachine (Machine Config Instruction Move)

namespace Lax119563Proofs.Computability

open CStm

/-! ## Representation of tapes -/

section Rep

variable (M : Machine)

/-- The stacks `L` and `R` represent tape `j` of `c`. -/
def RepT (c : Config M) (j : Fin (M.tapes + 1)) (L R : List ℕ) : Prop :=
  (∀ i : ℕ, (c.tape j (c.head j + i)).val = R.getD i 0) ∧
    ∀ i : ℕ, (c.tape j (c.head j - 1 - i)).val = L.getD i 0

variable {M}

lemma getD_lt_of_mem {l : List ℕ} {v B : ℕ} (hv : v ∈ l) (h : ∀ i, l.getD i 0 < B) : v < B := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  have := h i
  rwa [List.getD_eq_getElem _ _ hi] at this

lemma RepT.lt_L {c : Config M} {j : Fin (M.tapes + 1)} {L R : List ℕ} (h : RepT M c j L R)
    {v : ℕ} (hv : v ∈ L) : v < M.symbols + 3 :=
  getD_lt_of_mem hv fun i => by rw [← h.2 i]; exact Fin.isLt _

lemma RepT.headD {c : Config M} {j : Fin (M.tapes + 1)} {L R : List ℕ} (h : RepT M c j L R) :
    R.headD 0 = (c.tape j (c.head j)).val := by
  have := (h.1 0).symm
  simp only [Nat.cast_zero, add_zero] at this
  rw [← this]; cases R <;> rfl

/-- The new stacks after writing `a` and moving by `m` (the scanned cell popped from `R`). -/
def stepLR (a : ℕ) : Move → List ℕ → List ℕ → List ℕ × List ℕ
  | .stay, L, R => (L, a :: R)
  | .right, L, R => (a :: L, R)
  | .left, L, R => (L.tail, L.headD 0 :: a :: R)

lemma getD_tail (l : List ℕ) (i : ℕ) : l.tail.getD i 0 = l.getD (i + 1) 0 := by
  cases l <;> simp

lemma getD_zero_headD (l : List ℕ) : l.getD 0 0 = l.headD 0 := by
  cases l <;> simp

/-- One step on tape `j`: writing `a` and moving by `m`. -/
lemma RepT.step {c c' : Config M} {j : Fin (M.tapes + 1)} {L R : List ℕ} (h : RepT M c j L R)
    (a : Fin (M.symbols + 3)) (m : Move) (hh : c'.head j = c.head j + m.offset)
    (ht : c'.tape j = fun z => if z = c.head j then a else c.tape j z) :
    RepT M c' j (stepLR a.val m L R.tail).1 (stepLR a.val m L R.tail).2 := by
  obtain ⟨hR, hL⟩ := h
  unfold RepT
  cases m with
  | stay =>
    have hh' : c'.head j = c.head j := by simpa [Move.offset] using hh
    rw [hh', ht]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [stepLR]
      rcases i with _ | i
      · simp
      · rw [if_neg (by push_cast; omega), List.getD_cons_succ, getD_tail, ← hR]
    · simp only [stepLR]
      rw [if_neg (by omega), hL]
  | right =>
    have hh' : c'.head j = c.head j + 1 := by simpa [Move.offset] using hh
    rw [hh', ht]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [stepLR]
      rw [if_neg (by omega), getD_tail, ← hR]
      push_cast; ring_nf
    · simp only [stepLR]
      rcases i with _ | i
      · simp
      · rw [if_neg (by push_cast; omega), List.getD_cons_succ, ← hL]
        push_cast; ring_nf
  | left =>
    have hh' : c'.head j = c.head j + -1 := by simpa [Move.offset] using hh
    rw [hh', ht]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [stepLR]
      rcases i with _ | _ | i
      · rw [if_neg (by omega), List.getD_cons_zero, ← getD_zero_headD, ← hL]
        push_cast; ring_nf
      · simp
      · rw [if_neg (by push_cast; omega), List.getD_cons_succ, List.getD_cons_succ, getD_tail,
          ← hR]
        push_cast; ring_nf
    · simp only [stepLR]
      rw [if_neg (by omega), getD_tail, ← hL]
      push_cast; ring_nf

lemma getD_headD_tail (l : List ℕ) (i : ℕ) : (l.headD 0 :: l.tail).getD i 0 = l.getD i 0 := by
  cases l <;> cases i <;> simp

lemma stepLR_length (a : ℕ) (m : Move) (L R : List ℕ) :
    (stepLR a m L R).1.length ≤ L.length + 1 ∧ (stepLR a m L R).2.length ≤ R.length + 2 := by
  cases m <;> simp [stepLR] <;> omega

end Rep

/-! ## Sequences of per-tape statements -/

section Seq

variable {R Q n : ℕ} {x : List Bool} {w : ℕ}
variable (ρ : Rg n ↪ Fin R) (κ : Sk n ↪ Fin Q)

/-- The part of a state belonging to tape `j`. -/
def proj (st : NSt R Q) (j : Fin n) : List ℕ × List ℕ × ℕ :=
  (st.stk (κ (.L j)), st.stk (κ (.R j)), st.env (ρ (.sc j)))

/-- A per-tape statement with effect `E` on tape `j`. -/
def TapeOp (G : Fin n → CStm R Q) (E : Fin n → List ℕ × List ℕ × ℕ → List ℕ × List ℕ × ℕ) :
    Prop :=
  ∀ j (st : NSt R Q),
    proj ρ κ (exec x (G j) st) j = E j (proj ρ κ st j) ∧
    (∀ q, q ≠ κ (.L j) → q ≠ κ (.R j) → (exec x (G j) st).stk q = st.stk q) ∧
    (∀ r, r ≠ ρ .tmp → r ≠ ρ (.sc j) → (exec x (G j) st).env r = st.env r) ∧
    (exec x (G j) st).pos = st.pos ∧ (exec x (G j) st).out = st.out

lemma exec_seqL_cons (c : CStm R Q) (cs : List (CStm R Q)) (st : NSt R Q) :
    exec x (seqL (c :: cs)) st = exec x (seqL cs) (exec x c st) := rfl

lemma exec_seqL_tapes {G : Fin n → CStm R Q} {E : Fin n → List ℕ × List ℕ × ℕ → List ℕ × List ℕ × ℕ}
    (hG : TapeOp (x := x) ρ κ G E) :
    ∀ (l : List (Fin n)), l.Nodup → ∀ st : NSt R Q,
      (∀ j, proj ρ κ (exec x (seqL (l.map G)) st) j =
        if j ∈ l then E j (proj ρ κ st j) else proj ρ κ st j) ∧
      (∀ q, (∀ j ∈ l, q ≠ κ (.L j) ∧ q ≠ κ (.R j)) → (exec x (seqL (l.map G)) st).stk q = st.stk q) ∧
      (∀ r, r ≠ ρ .tmp → (∀ j ∈ l, r ≠ ρ (.sc j)) → (exec x (seqL (l.map G)) st).env r = st.env r) ∧
      (exec x (seqL (l.map G)) st).pos = st.pos ∧ (exec x (seqL (l.map G)) st).out = st.out
  | [], _, st => by simp [seqL, exec]
  | j₀ :: l, hnd, st => by
    have hj₀ : j₀ ∉ l := (List.nodup_cons.mp hnd).1
    obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ :=
      exec_seqL_tapes hG l (List.nodup_cons.mp hnd).2 (exec x (G j₀) st)
    obtain ⟨g1, g2, g3, g4, g5⟩ := hG j₀ st
    simp only [List.map_cons, exec_seqL_cons]
    refine ⟨fun j => ?_, fun q hq => ?_, fun r hr hr' => ?_, by rw [ih4, g4], by rw [ih5, g5]⟩
    · rw [ih1 j]
      by_cases hj : j = j₀
      · subst hj; simp [hj₀, g1]
      · have hp : proj ρ κ (exec x (G j₀) st) j = proj ρ κ st j := by
          simp only [proj]
          rw [g2 _ (by simpa using hj) (by simp), g2 _ (by simp) (by simpa using hj),
            g3 _ (by simp) (by simpa using hj)]
        by_cases hjl : j ∈ l
        · simp [hjl, hp]
        · simp [hjl, hj, hp]
    · rw [ih2 q (fun j hj => hq j (by simp [hj])), g2 q (hq j₀ (by simp)).1 (hq j₀ (by simp)).2]
    · rw [ih3 r hr (fun j hj => hr' j (by simp [hj])), g3 r hr (hr' j₀ (by simp))]

lemma good_seqL {ι : Type} {G : ι → CStm R Q} (Inv : NSt R Q → Prop) (C : ℕ)
    (hG : ∀ i st, Inv st → Good x w (G i) st (exec x (G i) st) C ∧ Inv (exec x (G i) st)) :
    ∀ (l : List ι) (st : NSt R Q), Inv st →
      Good x w (seqL (l.map G)) st (exec x (seqL (l.map G)) st) (l.length * C + unitCost w) ∧
        Inv (exec x (seqL (l.map G)) st)
  | [], st, h => ⟨(CStm.Good.skip (x := x) (w := w) (st := st)).mono (by simp), h⟩
  | i :: l, st, h => by
    obtain ⟨g, hi⟩ := hG i st h
    obtain ⟨g', hi'⟩ := good_seqL Inv C hG l _ hi
    refine ⟨(g.seq g').mono (by simp; ring_nf; omega), hi'⟩

/-! ## The per-tape statements -/

variable {M : Machine} (ρ : Rg (M.tapes + 1) ↪ Fin R) (κ : Sk (M.tapes + 1) ↪ Fin Q)

lemma popT_op : TapeOp (x := x) ρ κ (popT M ρ κ) fun _ p => (p.1, p.2.1.tail, p.2.1.headD 0) := by
  intro j st
  refine ⟨?_, fun q h1 h2 => ?_, fun r h1 h2 => ?_, rfl, rfl⟩
  · simp [proj, popT, exec, NSt.set, NSt.setS, Function.update_apply]
  · simp [popT, exec, NSt.set, NSt.setS, Function.update_apply, h2]
  · simp [popT, exec, NSt.set, NSt.setS, Function.update_apply, h2]

lemma pushT_op : TapeOp (x := x) ρ κ (pushT M ρ κ) fun _ p => (p.1, p.2.2 :: p.2.1, p.2.2) := by
  intro j st
  refine ⟨?_, fun q h1 h2 => ?_, fun r h1 h2 => ?_, rfl, rfl⟩
  · simp [proj, pushT, exec, NSt.set, NSt.setS, Function.update_apply, Ex.eval]
  · simp [pushT, exec, NSt.set, NSt.setS, Function.update_apply, h2]
  · simp [pushT, exec, NSt.set, NSt.setS, Function.update_apply]

lemma opT_op (a : Fin (M.tapes + 1) → ℕ) (m : Fin (M.tapes + 1) → Move) :
    TapeOp (x := x) ρ κ (fun j => opT M ρ κ j (a j) (m j))
      fun j p => ((stepLR (a j) (m j) p.1 p.2.1).1, (stepLR (a j) (m j) p.1 p.2.1).2, p.2.2) := by
  intro j st
  rcases hm : m j with _ | _ | _
  all_goals
    refine ⟨?_, fun q h1 h2 => ?_, fun r h1 h2 => ?_, ?_, ?_⟩
    · simp [proj, opT, hm, exec, NSt.set, NSt.setS, Function.update_apply, Ex.eval, stepLR]
    · simp [opT, hm, exec, NSt.set, NSt.setS, Function.update_apply, h1, h2]
    · simp [opT, hm, exec, NSt.set, NSt.setS, Function.update_apply, h1, h2]
    · simp [opT, hm, exec, NSt.set, NSt.setS]
    · simp [opT, hm, exec, NSt.set, NSt.setS]

end Seq

end Lax119563Proofs.Computability
