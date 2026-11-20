import Lax119563Proofs.Computability.SimTapes

/-!
# Simulating a machine: one iteration

`Inv st c t B h`: the state `st` of the simulator represents the configuration `c` of `M`
after `t` iterations, with halting flag `h`; the tape stacks have lengths at most `t` (left)
and `B + 2 t` (right). One iteration of the loop body simulates one step of `M`
(`iter_step`), within `bodyCost M w`.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax489179.TuringMachine (Machine Config Instruction Move)

namespace Lax119563Proofs.Computability

open CStm

variable {R Q : ℕ} {x : List Bool} {w : ℕ} {M : Machine}
variable (ρ : Rg (M.tapes + 1) ↪ Fin R) (κ : Sk (M.tapes + 1) ↪ Fin Q)

/-- The invariant of the simulation loop. -/
def Inv (st : NSt R Q) (c : Config M) (t B h : ℕ) : Prop :=
  st.env (ρ .st) = c.state.val ∧ st.env (ρ .halt) = h ∧ st.env (ρ .clk) = t ∧
    (∀ j, RepT M c j (st.stk (κ (.L j))) (st.stk (κ (.R j)))) ∧
    ∀ j, (st.stk (κ (.L j))).length ≤ t ∧ (st.stk (κ (.R j))).length ≤ B + 2 * t

variable (M) in
/-- The cost of one iteration. -/
noncomputable def bodyCost (w : ℕ) : ℕ :=
  ((keys M).length * (8 * (M.tapes + 1) + 12) + 10 * (M.tapes + 1) + 20) * Ex.nodeCost w

lemma chain_cons (p : Key M) (l : List (Key M)) :
    (chain M ρ κ (p :: l) : CStm R Q) = .ite (matchE M ρ p) (leaf M ρ κ p) (chain M ρ κ l) := rfl

lemma chain_good {l : List (Key M)} {p₀ : Key M} (hp : p₀ ∈ l) {st st' : NSt R Q} {T : ℕ}
    (hev : ∀ p, (matchE M ρ p).eval st.env = if p = p₀ then 1 else 0)
    (hf : ∀ p, (matchE M ρ p).Fits w st.env) (hl : Good x w (leaf M ρ κ p₀) st st' T) :
    Good x w (chain M ρ κ l) st st'
      (l.length * ((8 * (M.tapes + 1) + 11) * Ex.nodeCost w + 1) + T) := by
  induction l with
  | nil => simp at hp
  | cons p l ih =>
    rw [chain_cons]
    by_cases hpp : p = p₀
    · subst hpp
      refine (Good.iteT (hf p) (by rw [hev]; simp) hl).mono ?_
      simp only [condCost, matchE_size, List.length_cons]
      rw [add_one_mul]; exact Nat.add_le_add_right (Nat.le_add_left _ _) _
    · have hp' : p₀ ∈ l := by
        rcases List.mem_cons.mp hp with h | h
        · exact absurd h.symm hpp
        · exact h
      refine (Good.iteF (hf p) (by rw [hev, if_neg hpp]) (ih hp')).mono ?_
      simp only [condCost, matchE_size, List.length_cons]
      rw [add_one_mul]; linarith

lemma mem_keys (p : Key M) : p ∈ keys M := Finset.mem_toList.mpr (Finset.mem_univ _)

/-- Bounded left stacks. -/
def BndL (st : NSt R Q) : Prop := ∀ j, ∀ v ∈ st.stk (κ (.L j)), v < M.symbols + 3

lemma opT_good (hB : simB M ≤ 2 ^ w) (a : Fin (M.tapes + 1) → Fin (M.symbols + 3))
    (m : Fin (M.tapes + 1) → Move) (j : Fin (M.tapes + 1)) (st : NSt R Q) (hb : BndL κ st) :
    Good x w (opT M ρ κ j (a j).val (m j)) st (exec x (opT M ρ κ j (a j).val (m j)) st)
      (6 * Ex.nodeCost w) ∧ BndL κ (exec x (opT M ρ κ j (a j).val (m j)) st) := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have ha : (a j).val < 2 ^ w := by have := (a j).isLt; unfold simB at hB; omega
  obtain ⟨o1, o2, -⟩ := opT_op (x := x) ρ κ (fun j => (a j).val) m j st
  refine ⟨?_, fun j' v hv => ?_⟩
  · rcases hm : m j with _ | _ | _
    · simp only [opT]
      refine ((Good.pop _ _).seq ((Good.push ?_).seq (Good.push ?_))).mono ?_
      · simpa [Ex.Fits] using ha
      · simp only [Ex.Fits, NSt.setS_env, NSt.set_env, Function.update_self]
        rcases h : st.stk (κ (.L j)) with _ | ⟨v, l⟩
        · simp
        · have := hb j v (by simp [h]); simp; unfold simB at hB; omega
      · simp only [Ex.size]; omega
    · exact (Good.push (by simpa [Ex.Fits] using ha)).mono (by simp only [Ex.size]; omega)
    · exact (Good.push (by simpa [Ex.Fits] using ha)).mono (by simp only [Ex.size]; omega)
  · by_cases hj : j' = j
    · subst hj
      have h1 := congrArg Prod.fst o1
      simp only [proj] at h1
      rw [h1] at hv
      rcases hm : m j' with _ | _ | _ <;> simp only [hm, stepLR] at hv
      · exact hb j' v (List.mem_of_mem_tail hv)
      · exact hb j' v hv
      · rcases List.mem_cons.mp hv with rfl | hv
        · have := (a j').isLt; omega
        · exact hb j' v hv
    · rw [o2 _ (by simpa using hj) (by simp)] at hv
      exact hb j' v hv

lemma pushT_good (hB : simB M ≤ 2 ^ w) (j : Fin (M.tapes + 1)) (st : NSt R Q)
    (hb : ∀ j, st.env (ρ (.sc j)) < M.symbols + 3) :
    Good x w (pushT M ρ κ j) st (exec x (pushT M ρ κ j) st) (2 * Ex.nodeCost w) ∧
      ∀ j, (exec x (pushT M ρ κ j) st).env (ρ (.sc j)) < M.symbols + 3 := by
  have hU := Ex.unitCost_le_nodeCost w
  refine ⟨(Good.push ?_).mono ?_, fun j' => hb j'⟩
  · simp only [Ex.Fits]; have := hb j; unfold simB at hB; omega
  · simp only [Ex.size]; omega

lemma iter_step (hB : simB M ≤ 2 ^ w) {st : NSt R Q} {c : Config M} {t B : ℕ}
    (hI : Inv ρ κ st c t B 0) (hc : c.answer = none) (ht : t + 1 < 2 ^ w) :
    Good x w (body M ρ κ) st (exec x (body M ρ κ) st) (bodyCost M w) ∧
      Inv ρ κ (exec x (body M ρ κ) st) (Lax489179.TuringMachine.step M false c) (t + 1) B
        (if (Lax489179.TuringMachine.step M false c).answer.isSome then 1 else 0) := by
  obtain ⟨hst, hhalt, hclk, hrep, hlen⟩ := hI
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have hl : (List.finRange (M.tapes + 1)).Nodup := List.nodup_finRange _
  have hmem : ∀ j, j ∈ List.finRange (M.tapes + 1) := List.mem_finRange
  -- popping the scanned symbols
  set st1 := exec x (seqL ((List.finRange (M.tapes + 1)).map (popT M ρ κ))) st with hst1
  obtain ⟨p1, -, p3, p4, p5⟩ := exec_seqL_tapes (x := x) ρ κ (popT_op ρ κ) _ hl st
  have e1 : ∀ j, st1.stk (κ (.L j)) = st.stk (κ (.L j)) ∧
      st1.stk (κ (.R j)) = (st.stk (κ (.R j))).tail ∧
      st1.env (ρ (.sc j)) = (c.tape j (c.head j)).val := by
    intro j
    have := p1 j
    simp only [proj, hmem, if_true, Prod.mk.injEq] at this
    exact ⟨this.1, this.2.1, this.2.2.trans (hrep j).headD⟩
  have e1r : ∀ g : Rg (M.tapes + 1), (∀ j, g ≠ .sc j) → g ≠ .tmp → st1.env (ρ g) = st.env (ρ g) :=
    fun g hg ht => p3 _ (by simpa using ht) (fun j _ => by simpa using hg j)
  have g1 : Good x w (seqL ((List.finRange (M.tapes + 1)).map (popT M ρ κ))) st st1
      ((M.tapes + 1) * (unitCost w + 1) + unitCost w) := by
    have := good_seqL (x := x) (w := w) (G := popT M ρ κ) (fun _ => True) (unitCost w + 1)
      (fun j st _ => ⟨Good.pop _ _, trivial⟩) (List.finRange (M.tapes + 1)) st trivial
    simpa using this.1
  -- the key
  set p₀ : Key M := (c.state, fun j => c.tape j (c.head j)) with hp₀
  have est1 : st1.env (ρ .st) = c.state.val := by rw [e1r .st (by simp) (by simp), hst]
  have hev : ∀ p, (matchE M ρ p).eval st1.env = if p = p₀ then 1 else 0 := by
    intro p
    rw [matchE_eval]
    refine if_congr ⟨fun ⟨h1, h2⟩ => ?_, fun h => ?_⟩ rfl rfl
    · refine Prod.ext (Fin.ext (by rw [← h1, est1])) (funext fun j => Fin.ext ?_)
      rw [← h2 j, (e1 j).2.2]
    · subst h; exact ⟨est1, fun j => (e1 j).2.2⟩
  have hfits : ∀ p, (matchE M ρ p).Fits w st1.env := fun p =>
    matchE_fits M ρ _ p hB (by rw [est1]; have := c.state.isLt; unfold simB at hB; omega)
      (fun j => by rw [(e1 j).2.2]; have := (c.tape j (c.head j)).isLt; unfold simB at hB; omega)
  have hclk1 : st1.env (ρ .clk) = t := by rw [e1r .clk (by simp) (by simp), hclk]
  -- the leaf
  cases htr : M.transition c.state (fun j => c.tape j (c.head j)) false with
  | halt b =>
    have hleaf : (leaf M ρ κ p₀ : CStm R Q) = .seq (.set (ρ .halt) (.const 1))
        (seqL ((List.finRange (M.tapes + 1)).map (pushT M ρ κ))) := by
      simp only [leaf, hp₀]; rw [htr]
    set st2 := st1.set (ρ .halt) 1 with hst2
    set st3 := exec x (seqL ((List.finRange (M.tapes + 1)).map (pushT M ρ κ))) st2 with hst3
    obtain ⟨q1, -, q3, q4, q5⟩ := exec_seqL_tapes (x := x) ρ κ (pushT_op ρ κ) _ hl st2
    have hpush := good_seqL (x := x) (w := w) (G := pushT M ρ κ)
      (fun st => ∀ j, st.env (ρ (.sc j)) < M.symbols + 3) (2 * Ex.nodeCost w)
      (fun j st h => pushT_good ρ κ hB j st h) (List.finRange (M.tapes + 1)) st2
      (fun j => by
        simp only [hst2, NSt.set_env, Function.update_of_ne (by simp : ρ (.sc j) ≠ ρ .halt)]
        rw [(e1 j).2.2]; exact Fin.isLt _)
    have g2 : Good x w (leaf M ρ κ p₀) st1 st3 ((M.tapes + 3) * (2 * Ex.nodeCost w)) := by
      rw [hleaf]
      refine ((Good.set (by simp only [Ex.Fits]; omega)).seq hpush.1).mono ?_
      simp only [Ex.size, List.length_finRange]; nlinarith
    have g3 := chain_good ρ κ (mem_keys p₀) hev hfits g2
    have hclk3 : st3.env (ρ .clk) = t := by
      rw [q3 _ (by simp) (by simp)]; simp only [hst2, NSt.set_env]
      rw [Function.update_of_ne (by simp)]; exact hclk1
    have g4 : Good x w (.set (ρ .clk) (.add (.var (ρ .clk)) (.const 1))) st3
        (st3.set (ρ .clk) (t + 1)) (3 * Ex.nodeCost w + unitCost w) :=
      (Good.set (by simp only [Ex.Fits, Ex.eval, hclk3]; omega)).of_eq
        (by simp [Ex.eval, hclk3]) (by simp [Ex.size])
    have gb : Good x w (body M ρ κ) st (st3.set (ρ .clk) (t + 1)) _ := g1.seq (g3.seq g4)
    have hex : exec x (body M ρ κ) st = st3.set (ρ .clk) (t + 1) := gb.2.1
    refine ⟨?_, ?_⟩
    · rw [hex]; refine gb.mono ?_
      simp only [bodyCost]; nlinarith
    rw [hex]
    have hstep : Lax489179.TuringMachine.step M false c = { c with answer := some b } := by
      simp [Lax489179.TuringMachine.step, hc, htr]
    rw [hstep]
    refine ⟨?_, ?_, by simp, fun j => ?_, fun j => ?_⟩
    · simp only [NSt.set_env, Function.update_of_ne (by simp : ρ .st ≠ ρ .clk)]
      rw [q3 _ (by simp) (by simp)]
      simp only [hst2, NSt.set_env, Function.update_of_ne (by simp : ρ .st ≠ ρ .halt)]
      exact est1
    · simp only [NSt.set_env, Function.update_of_ne (by simp : ρ .halt ≠ ρ .clk), Option.isSome_some,
        if_true]
      rw [q3 _ (by simp) (by simp)]; simp [hst2]
    · have := q1 j
      simp only [proj, hmem, if_true, Prod.mk.injEq] at this
      simp only [NSt.set_stk]
      rw [this.1, this.2.1]
      simp only [hst2, NSt.set_stk, NSt.set_env, Function.update_of_ne (by simp : ρ (.sc j) ≠ ρ .halt)]
      rw [(e1 j).1, (e1 j).2.1, (e1 j).2.2]
      obtain ⟨r1, r2⟩ := hrep j
      refine ⟨fun i => ?_, fun i => r2 i⟩
      rw [← (hrep j).headD, getD_headD_tail]; exact r1 i
    · have := q1 j
      simp only [proj, hmem, if_true, Prod.mk.injEq] at this
      simp only [NSt.set_stk]
      rw [this.1, this.2.1]
      simp only [hst2, NSt.set_stk]
      rw [(e1 j).1, (e1 j).2.1]
      have := hlen j
      simp only [List.length_cons, List.length_tail]
      omega
  | next q' wr mv =>
    have hleaf : (leaf M ρ κ p₀ : CStm R Q) = .seq (.set (ρ .st) (.const q'.val))
        (seqL ((List.finRange (M.tapes + 1)).map fun j => opT M ρ κ j (wr j).val (mv j))) := by
      simp only [leaf, hp₀]; rw [htr]
    set st2 := st1.set (ρ .st) q'.val with hst2
    set st3 := exec x (seqL ((List.finRange (M.tapes + 1)).map
      fun j => opT M ρ κ j (wr j).val (mv j))) st2 with hst3
    obtain ⟨q1, -, q3, q4, q5⟩ := exec_seqL_tapes (x := x) ρ κ
      (opT_op ρ κ (fun j => (wr j).val) mv) _ hl st2
    have hop := good_seqL (x := x) (w := w) (G := fun j => opT M ρ κ j (wr j).val (mv j))
      (BndL κ) (6 * Ex.nodeCost w)
      (fun j st h => opT_good ρ κ hB wr mv j st h) (List.finRange (M.tapes + 1)) st2
      (fun j v hv => by
        simp only [hst2, NSt.set_stk] at hv
        rw [(e1 j).1] at hv
        exact (hrep j).lt_L hv)
    have hq' : q'.val < 2 ^ w := by have := q'.isLt; unfold simB at hB; omega
    have g2 : Good x w (leaf M ρ κ p₀) st1 st3 ((M.tapes + 3) * (6 * Ex.nodeCost w)) := by
      rw [hleaf]
      refine ((Good.set (by simp only [Ex.Fits]; omega)).seq hop.1).mono ?_
      simp only [Ex.size, List.length_finRange]; nlinarith
    have g3 := chain_good ρ κ (mem_keys p₀) hev hfits g2
    have hclk3 : st3.env (ρ .clk) = t := by
      rw [q3 _ (by simp) (by simp)]; simp only [hst2, NSt.set_env]
      rw [Function.update_of_ne (by simp)]; exact hclk1
    have g4 : Good x w (.set (ρ .clk) (.add (.var (ρ .clk)) (.const 1))) st3
        (st3.set (ρ .clk) (t + 1)) (3 * Ex.nodeCost w + unitCost w) :=
      (Good.set (by simp only [Ex.Fits, Ex.eval, hclk3]; omega)).of_eq
        (by simp [Ex.eval, hclk3]) (by simp [Ex.size])
    have gb : Good x w (body M ρ κ) st (st3.set (ρ .clk) (t + 1)) _ := g1.seq (g3.seq g4)
    have hex : exec x (body M ρ κ) st = st3.set (ρ .clk) (t + 1) := gb.2.1
    refine ⟨?_, ?_⟩
    · rw [hex]; refine gb.mono ?_
      simp only [bodyCost]; nlinarith
    rw [hex]
    have hstep : Lax489179.TuringMachine.step M false c =
        { state := q', head := fun j => c.head j + (mv j).offset,
          tape := fun j z => if z = c.head j then wr j else c.tape j z, answer := none } := by
      simp [Lax489179.TuringMachine.step, hc, htr]
    rw [hstep]
    refine ⟨?_, ?_, by simp, fun j => ?_, fun j => ?_⟩
    · simp only [NSt.set_env, Function.update_of_ne (by simp : ρ .st ≠ ρ .clk)]
      rw [q3 _ (by simp) (by simp)]
      simp [hst2]
    · simp only [NSt.set_env, Function.update_of_ne (by simp : ρ .halt ≠ ρ .clk),
        Option.isSome_none, Bool.false_eq_true, if_false]
      rw [q3 _ (by simp) (by simp)]
      simp only [hst2, NSt.set_env, Function.update_of_ne (by simp : ρ .halt ≠ ρ .st)]
      rw [e1r .halt (by simp) (by simp), hhalt]
    · have := q1 j
      simp only [proj, hmem, if_true, Prod.mk.injEq] at this
      simp only [NSt.set_stk]
      rw [this.1, this.2.1]
      simp only [hst2, NSt.set_stk]
      rw [(e1 j).1, (e1 j).2.1]
      exact (hrep j).step (wr j) (mv j) rfl rfl
    · have := q1 j
      simp only [proj, hmem, if_true, Prod.mk.injEq] at this
      simp only [NSt.set_stk]
      rw [this.1, this.2.1]
      simp only [hst2, NSt.set_stk]
      rw [(e1 j).1, (e1 j).2.1]
      have h1 := stepLR_length (wr j).val (mv j) (st.stk (κ (.L j))) (st.stk (κ (.R j))).tail
      have := hlen j
      simp only [List.length_tail] at h1
      omega

end Lax119563Proofs.Computability
