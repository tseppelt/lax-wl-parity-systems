import Lax119563Proofs.Computability.SimFull

/-!
# Simulating a machine: specifications

* `simNat_good`: if `M` computes `encodeNat v` from `encodeNat k` (`k` the value of `inp`),
  the simulator `simNat M ρ κ` sets `out := v` and `clk := haltTime M (encodeNat k)`;
* `simIn_good`: the same for `simIn M ρ κ` and the input `x` of the statement.

Both require the word size to be large enough (`simB M ≤ 2 ^ w`, the halting time below
`2 ^ w`, `v` with fewer than `w` binary digits), all stacks of the simulator to be empty
before (they are empty afterwards), and all values to be below `2 ^ w` (`NSt.Bdd`).
Registers outside the range of `ρ`, stacks outside the range of `κ` and the output are
kept; `simNat` also keeps the cursor.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax119563.DeterministicTime
open Lax489179.TuringMachine (Machine Config Instruction Move)

namespace Lax119563Proofs.Computability

open CStm

variable {R Q : ℕ} {x : List Bool} {w : ℕ} {M : Machine}
variable (ρ : Rg (M.tapes + 1) ↪ Fin R) (κ : Sk (M.tapes + 1) ↪ Fin Q)

/-! ## Costs -/

variable (M) in
/-- The cost of `simTail` with input length `a` and halting time `s`. -/
noncomputable def tailCost (w a s : ℕ) : ℕ :=
  coreCost M w s + (extractCost w s a +
    ((allSk (M.tapes + 1)).length * ((a + 3 * s + 1) * (8 * Ex.nodeCost w)) + unitCost w +
      unitCost w))

/-- The cost of loading a number with a code of length `a`. -/
def loadNatCost (w a : ℕ) : ℕ := (a + 2) * (30 * Ex.nodeCost w)

/-- The cost of loading an input of length `a`. -/
def loadInCost (w a : ℕ) : ℕ := (a + 2) * (30 * Ex.nodeCost w)

/-! ## Clearing -/

lemma clear_list (hw : 2 ≤ w) (Λ : ℕ) : ∀ (l : List (Sk (M.tapes + 1))) (st : NSt R Q),
    (∀ g ∈ l, (st.stk (κ g)).length ≤ Λ) →
    Good x w (seqL (l.map fun g => clrS (κ g) (ρ .tmp) (ρ .flg))) st
        (exec x (seqL (l.map fun g => clrS (κ g) (ρ .tmp) (ρ .flg))) st)
        (l.length * ((Λ + 1) * (8 * Ex.nodeCost w)) + unitCost w) ∧
      ∀ g ∈ l, (exec x (seqL (l.map fun g => clrS (κ g) (ρ .tmp) (ρ .flg))) st).stk (κ g) = []
  | [], st, _ => ⟨(CStm.Good.skip (x := x) (w := w) (st := st)).mono (by simp), by simp⟩
  | g :: l, st, h => by
    obtain ⟨g1, e1, e2⟩ := clrS_good (x := x) hw (q := κ g) (t := ρ .tmp) (f := ρ .flg)
      (by simp) st
    set st1 := exec x (clrS (κ g) (ρ .tmp) (ρ .flg)) st with hst1
    have h1 : ∀ g' ∈ l, (st1.stk (κ g')).length ≤ Λ := fun g' hg' => by
      by_cases hgg : g' = g
      · subst hgg; rw [e1]; simp
      · rw [e2 _ (by simpa using hgg)]; exact h g' (by simp [hg'])
    obtain ⟨g2, e3⟩ := clear_list hw Λ l st1 h1
    refine ⟨(g1.seq g2).mono ?_, fun g' hg' => ?_⟩
    · have := h g (by simp)
      simp only [List.length_cons]
      have : ((st.stk (κ g)).length + 1) * (8 * Ex.nodeCost w) ≤
          (Λ + 1) * (8 * Ex.nodeCost w) := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    · simp only [List.map_cons, exec_seqL_cons]
      by_cases hgl : g' ∈ l
      · exact e3 g' hgl
      · have hg : g' = g := by
          rcases List.mem_cons.mp hg' with h | h
          · exact h
          · exact absurd h hgl
        subst hg
        rw [exec_stk_of _ _ (wStk_seqL_map _ _ fun g'' hg'' => by
          simpa [clrS, wStk] using (fun h : g'' = g' => hgl (h ▸ hg'')))]
        exact e1

/-! ## The tail -/

theorem tail_good (hw : 2 ≤ w) (hB : simB M ≤ 2 ^ w) (st : NSt R Q) (hb : st.Bdd w)
    (hp : st.pos ≤ x.length) (u : List Bool)
    (hstk : ∀ g, st.stk (κ g) = if g = .R 0 then syms u else [])
    {v t : ℕ} (hM : ComputesWithin M u (encodeNat v) t) (hs : haltTime M u < 2 ^ w)
    (hv : v.bits.length < w) :
    Good x w (simTail M ρ κ) st (exec x (simTail M ρ κ) st)
        (tailCost M w u.length (haltTime M u)) ∧
      (exec x (simTail M ρ κ) st).env (ρ .out) = v ∧
      (exec x (simTail M ρ κ) st).env (ρ .clk) = haltTime M u ∧
      ∀ g, (exec x (simTail M ρ κ) st).stk (κ g) = [] := by
  have hL : ∀ j, st.stk (κ (.L j)) = [] := fun j => by rw [hstk]; simp
  have hR : ∀ j, st.stk (κ (.R j)) = if j = 0 then u.map symOf else [] := fun j => by
    rw [hstk]; by_cases hj : j = 0 <;> simp [hj, syms]
  have hh : ∃ t, (runOn M u t).answer.isSome := ⟨t, hM.1⟩
  obtain ⟨gc, hI⟩ := core_good ρ κ (x := x) hB u st hL hR hh hs
  set s := haltTime M u with hsdef
  set st1 := exec x (core M ρ κ) st with hst1
  have hbd := CStm.Good.bdd hw gc hb hp
  have hc : (runOn M u s).tape 0 = (Lax489179.TuringMachine.init M (encodeNat v)).tape 0 :=
    (ComputesWithin.haltTime hM).1.2
  obtain ⟨ge, eo, eR, eL, eq⟩ := extract_good ρ κ (x := x) hw st1 hbd.1 hI
    (Main.Compose.head_natAbs_le M u 0 _) hc hv
  set st2 := exec x (extract M ρ κ) st1 with hst2
  have hlen := hI.2.2.2.2
  have hΛ : ∀ g, (st2.stk (κ g)).length ≤ u.length + 3 * s := by
    intro g
    cases g with
    | aux =>
      rw [eq _ (by simp) (by simp), hst1,
        exec_stk_of _ _ (wStk_core' ρ κ fun j => ⟨by simp, by simp⟩), hstk]
      simp
    | L j =>
      by_cases hj : j = 0
      · subst hj; rw [eL]; simp
      · rw [eq _ (by simpa using hj) (by simp)]; have := (hlen j).1; omega
    | R j =>
      by_cases hj : j = 0
      · subst hj; exact eR
      · rw [eq _ (by simp) (by simpa using hj)]; have := (hlen j).2; omega
  obtain ⟨gcl, ecl⟩ := clear_list ρ κ (x := x) hw (u.length + 3 * s) (allSk (M.tapes + 1)) st2
    (fun g _ => hΛ g)
  set st3 := exec x (clearAll M ρ κ) st2 with hst3
  have g : Good x w (simTail M ρ κ) st st3 _ := gc.seq (ge.seq (gcl.seq CStm.Good.skip))
  have hex : exec x (simTail M ρ κ) st = st3 := g.2.1
  refine ⟨?_, ?_, ?_, fun g' => ?_⟩
  · rw [hex]; exact g.mono (by simp only [tailCost]; omega)
  · rw [hex, hst3, exec_env_of _ _ (show wReg _ (clearAll M ρ κ : CStm R Q) = false from
      wReg_seqL_map _ _ fun g _ => by simp [clrS, wReg]), eo]
  · rw [hex, hst3, exec_env_of _ _ (show wReg _ (clearAll M ρ κ : CStm R Q) = false from
      wReg_seqL_map _ _ fun g _ => by simp [clrS, wReg]), hst2,
      exec_env_of _ _ (by simp [extract, seqL, wReg, moveAllS, skipZ, parseB])]
    exact hI.2.2.1
  · rw [hex]; exact ecl g' (mem_allSk g')

/-! ## Loading -/

lemma loadNat_good (hw : 2 ≤ w) (st : NSt R Q) (hb : st.Bdd w) (hp : st.pos ≤ x.length)
    (hemp : ∀ g, st.stk (κ g) = []) {k : ℕ} (hk : st.env (ρ .inp) = k) (hkw : k < 2 ^ w) :
    Good x w (loadNat M ρ κ) st (exec x (loadNat M ρ κ) st)
        (loadNatCost w (encodeNat k).length) ∧
      ∀ g, (exec x (loadNat M ρ κ) st).stk (κ g) =
        if g = .R 0 then syms (encodeNat k) else [] := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  have h1 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  set st1 := st.set (ρ .tmp) k with hst1
  have g1 : Good x w (.set (ρ .tmp) (.var (ρ .inp)) : CStm R Q) st st1
      (Ex.nodeCost w + unitCost w) := by
    have e : st1 = st.set (ρ .tmp) ((Ex.var (ρ .inp) : Ex R).eval st.env) := by
      simp [hst1, Ex.eval, hk]
    rw [e]; exact (CStm.Good.set (by simp [Ex.Fits, hk, hkw])).mono (by simp [Ex.size])
  obtain ⟨g2, e2stk, -, -⟩ := pushBits_good (x := x) (q := κ .aux) (t := ρ .tmp) hw st1 k (by simp [hst1])
    hkw
  set st2 := exec x (pushBits (κ .aux) (ρ .tmp)) st1 with hst2
  set st3 := st2.setS (κ .aux) (1 :: st2.stk (κ .aux)) with hst3
  have g3 : Good x w (.push (κ .aux) (.const 1) : CStm R Q) st2 st3 (Ex.nodeCost w + unitCost w) :=
    (CStm.Good.push (by simp [Ex.Fits, h1])).of_eq (by simp [hst3, Ex.eval]) (by simp [Ex.size])
  have hbd3 := CStm.Good.bdd hw (g1.seq (g2.seq g3)) hb hp
  obtain ⟨st4, g4, e4stk, -, -, -⟩ := moveAllS_good (x := x) hw (q := κ .aux) (q' := κ (.R 0))
    (t := ρ .tmp) (f := ρ .flg) (by simp) (by simp) st3 hbd3.1
  have g : Good x w (loadNat M ρ κ) st _ _ := g1.seq (g2.seq (g3.seq (g4.seq CStm.Good.skip)))
  have hex := g.2.1
  have hs2 : ∀ g, g ≠ .aux → st2.stk (κ g) = [] := fun g hg => by
    rw [hst2, exec_stk_of _ _ (by simp [pushBits, seqL, wStk, Ne.symm hg])]
    simp [hst1, hemp]
  have haux3 : st3.stk (κ .aux) = 1 :: (syms (pairs k.bits)).reverse := by
    simp [hst3, e2stk, hst1, hemp]
  refine ⟨?_, fun g' => ?_⟩
  · rw [hex]; refine g.mono ?_
    simp only [loadNatCost, haux3, List.length_cons, List.length_reverse, syms, List.length_map,
      length_pairs, length_encodeNat]
    nlinarith
  · rw [hex, e4stk]
    by_cases hg : g' = .R 0
    · subst hg
      have h3 : st3.stk (κ (.R 0)) = [] := by
        rw [hst3, NSt.setS_stk, Function.update_of_ne (by simp), hs2 _ (by simp)]
      rw [Function.update_self, if_pos rfl, haux3, h3]
      simp [syms, encodeNat_eq_pairs, symOf]
    · rw [if_neg hg, Function.update_of_ne (by simpa using hg)]
      by_cases hg' : g' = .aux
      · subst hg'; simp
      · rw [Function.update_of_ne (by simpa using hg'), hst3, NSt.setS_stk,
          Function.update_of_ne (by simpa using hg'), hs2 _ hg']

lemma loadIn_good (hw : 2 ≤ w) (st : NSt R Q) (hb : st.Bdd w) (hp : st.pos ≤ x.length)
    (hemp : ∀ g, st.stk (κ g) = []) :
    Good x w (loadIn M ρ κ) st (exec x (loadIn M ρ κ) st) (loadInCost w x.length) ∧
      (∀ g, (exec x (loadIn M ρ κ) st).stk (κ g) = if g = .R 0 then syms x else []) ∧
      (exec x (loadIn M ρ κ) st).pos = x.length := by
  have hU := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  set st1 : NSt R Q := { st with pos := 0 } with hst1
  have g1 : Good x w (.rst : CStm R Q) st st1 (unitCost w * (x.length + 1)) :=
    CStm.Good.rst.mono (Nat.mul_le_mul_left _ (by omega))
  obtain ⟨g2, e2stk, -, -, e2pos⟩ := readIn_good (x := x) (q := κ .aux) (t := ρ .tmp) hw st1 rfl
  set st2 := exec x (readIn (κ .aux) (ρ .tmp)) st1 with hst2
  have hbd2 := CStm.Good.bdd hw (g1.seq g2) hb hp
  obtain ⟨st3, g3, e3stk, e3pos, -, -⟩ := moveAllS_good (x := x) hw (q := κ .aux) (q' := κ (.R 0))
    (t := ρ .tmp) (f := ρ .flg) (by simp) (by simp) st2 hbd2.1
  have g : Good x w (loadIn M ρ κ) st _ _ := g1.seq (g2.seq (g3.seq CStm.Good.skip))
  have hex := g.2.1
  have hs2 : ∀ g, g ≠ .aux → st2.stk (κ g) = [] := fun g hg => by
    rw [hst2, exec_stk_of _ _ (by simp [readIn, wStk, Ne.symm hg])]
    simp [hst1, hemp]
  have haux2 : st2.stk (κ .aux) = (syms x).reverse := by simp [e2stk, hst1, hemp]
  refine ⟨?_, fun g' => ?_, by rw [hex, e3pos, e2pos]⟩
  · rw [hex]; refine g.mono ?_
    simp only [loadInCost, haux2, List.length_reverse, syms, List.length_map]
    nlinarith
  · rw [hex, e3stk]
    by_cases hg : g' = .R 0
    · subst hg
      simp only [Function.update_self, if_true, haux2, List.reverse_reverse]
      rw [hs2 _ (by simp), List.append_nil]
    · rw [if_neg hg, Function.update_of_ne (by simpa using hg)]
      by_cases hg' : g' = .aux
      · subst hg'; simp
      · rw [Function.update_of_ne (by simpa using hg'), hs2 _ hg']

/-! ## The simulators -/

variable (M) in
/-- The cost bound of `simNat` (code length `a` of the input number, halting time `s`). -/
noncomputable def simNatCost (w a s : ℕ) : ℕ := loadNatCost w a + tailCost M w a s

variable (M) in
/-- The cost bound of `simIn` (input length `a`, halting time `s`). -/
noncomputable def simInCost (w a s : ℕ) : ℕ := loadInCost w a + tailCost M w a s

/-- **The simulator on a number.** -/
theorem simNat_good (hw : 2 ≤ w) (hB : simB M ≤ 2 ^ w) (st : NSt R Q) (hb : st.Bdd w)
    (hp : st.pos ≤ x.length) (hemp : ∀ g, st.stk (κ g) = []) {k v t : ℕ}
    (hk : st.env (ρ .inp) = k) (hkw : k < 2 ^ w)
    (hM : ComputesWithin M (encodeNat k) (encodeNat v) t)
    (hs : haltTime M (encodeNat k) < 2 ^ w) (hv : v.bits.length < w) :
    Good x w (simNat M ρ κ) st (exec x (simNat M ρ κ) st)
        (simNatCost M w (encodeNat k).length (haltTime M (encodeNat k))) ∧
      (exec x (simNat M ρ κ) st).env (ρ .out) = v ∧
      (exec x (simNat M ρ κ) st).env (ρ .clk) = haltTime M (encodeNat k) ∧
      (∀ g, (exec x (simNat M ρ κ) st).stk (κ g) = []) ∧
      (∀ r, (∀ g, ρ g ≠ r) → (exec x (simNat M ρ κ) st).env r = st.env r) ∧
      (∀ q, (∀ g, κ g ≠ q) → (exec x (simNat M ρ κ) st).stk q = st.stk q) ∧
      (exec x (simNat M ρ κ) st).pos = st.pos ∧ (exec x (simNat M ρ κ) st).out = st.out := by
  obtain ⟨g1, e1⟩ := loadNat_good ρ κ (x := x) hw st hb hp hemp hk hkw
  have hbd := CStm.Good.bdd hw g1 hb hp
  obtain ⟨g2, e2o, e2c, e2s⟩ := tail_good ρ κ (x := x) hw hB _ hbd.1 hbd.2 _ e1 hM hs hv
  have g : Good x w (simNat M ρ κ) st _ _ := g1.seq g2
  have hex : exec x (simNat M ρ κ) st = _ := g.2.1
  refine ⟨?_, ?_, ?_, ?_, fun r hr => exec_env_of _ _ (wReg_simNat ρ κ hr),
    fun q hq => exec_stk_of _ _ (wStk_simNat ρ κ hq), exec_pos_of _ _ (wPos_simNat ρ κ),
    exec_out_of _ _ (wOut_simNat ρ κ)⟩
  · rw [hex]; exact g.mono le_rfl
  · rw [hex]; exact e2o
  · rw [hex]; exact e2c
  · rw [hex]; exact e2s

/-- **The simulator on the input.** -/
theorem simIn_good (hw : 2 ≤ w) (hB : simB M ≤ 2 ^ w) (st : NSt R Q) (hb : st.Bdd w)
    (hp : st.pos ≤ x.length) (hemp : ∀ g, st.stk (κ g) = []) {v t : ℕ}
    (hM : ComputesWithin M x (encodeNat v) t)
    (hs : haltTime M x < 2 ^ w) (hv : v.bits.length < w) :
    Good x w (simIn M ρ κ) st (exec x (simIn M ρ κ) st)
        (simInCost M w x.length (haltTime M x)) ∧
      (exec x (simIn M ρ κ) st).env (ρ .out) = v ∧
      (exec x (simIn M ρ κ) st).env (ρ .clk) = haltTime M x ∧
      (∀ g, (exec x (simIn M ρ κ) st).stk (κ g) = []) ∧
      (∀ r, (∀ g, ρ g ≠ r) → (exec x (simIn M ρ κ) st).env r = st.env r) ∧
      (∀ q, (∀ g, κ g ≠ q) → (exec x (simIn M ρ κ) st).stk q = st.stk q) ∧
      (exec x (simIn M ρ κ) st).pos = x.length ∧ (exec x (simIn M ρ κ) st).out = st.out := by
  obtain ⟨g1, e1, e1p⟩ := loadIn_good ρ κ (x := x) hw st hb hp hemp
  have hbd := CStm.Good.bdd hw g1 hb hp
  obtain ⟨g2, e2o, e2c, e2s⟩ := tail_good ρ κ (x := x) hw hB _ hbd.1 hbd.2 _ e1 hM hs hv
  have g : Good x w (simIn M ρ κ) st _ _ := g1.seq g2
  have hex : exec x (simIn M ρ κ) st = _ := g.2.1
  refine ⟨?_, ?_, ?_, ?_, fun r hr => exec_env_of _ _ (wReg_simIn ρ κ hr),
    fun q hq => exec_stk_of _ _ (wStk_simIn ρ κ hq), ?_, exec_out_of _ _ (wOut_simIn ρ κ)⟩
  · rw [hex]; exact g.mono le_rfl
  · rw [hex]; exact e2o
  · rw [hex]; exact e2c
  · rw [hex]; exact e2s
  · rw [hex, exec_pos_of _ _ (wPos_tail ρ κ), e1p]

end Lax119563Proofs.Computability
