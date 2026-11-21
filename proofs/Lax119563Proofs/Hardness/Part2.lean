import Lax119563.ParameterizedComplexity
import Lax119563Proofs.Compiler.Part1
import Lax119563Proofs.Compiler.Part2
import Lax119563Proofs.Compiler.Part6
import Lax119563Proofs.Hardness.Part1

/-! ### Formerly `Lax119563Proofs.Computability.SimSpec` -/

section Computability_SimSpec

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

end Computability_SimSpec

/-! ### Formerly `Lax119563Proofs.Computability.Bridge` -/

section Computability_Bridge

/-!
# From structured statements to computable functions

* `machineComputable_of_stm`: a statement that, on the input `encodeNat k`, emits exactly
  `f k` (for some word size, from the zero state) yields `MachineComputable f`;
* register layouts `slot` for simulators inside larger statements (several simulators may
  share the same registers and stacks, since they run one after the other);
* the simulator in this layout, from a state with all stacks empty: `simNat_slot`.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax119563.DeterministicTime Lax119563.ParameterizedComplexity
open Lax489179.TuringMachine (Machine Config Instruction Move Deterministic)

namespace Lax119563Proofs.Computability

open CStm

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

/-! ## The bridge -/

lemma encodeNats_singleton (v : ℕ) : encodeNats [v] = encodeNat v := by simp [encodeNats]

lemma bdd_zero (R Q w : ℕ) : (NSt.zero R Q).Bdd w :=
  ⟨fun _ => by simp [NSt.zero], fun _ v hv => by simp [NSt.zero] at hv⟩

/-- **Statements compute functions.** -/
theorem machineComputable_of_stm (c : CStm R Q) (f : ℕ → ℕ)
    (h : ∀ k, ∃ w, 2 ≤ w ∧ ∃ st' T, Good (encodeNat k) w c (NSt.zero R Q) st' T ∧
      st'.out = [f k]) : MachineComputable f := by
  refine ⟨c.machine c.depth, CStm.machine_deterministic _ _, fun k => ?_⟩
  obtain ⟨w, hw, st', T, hg, ho⟩ := h k
  have := CStm.computesWithin (D := c.depth) hw le_rfl hg.1
  rw [hg.2.1, ho, encodeNats_singleton] at this
  exact ⟨_, this⟩

/-! ## Arithmetic facts -/

lemma bits_length_le (v : ℕ) : v.bits.length ≤ v := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · simp [Nat.zero_bits]
    · rw [bits_eq_cons hv.ne', List.length_cons]
      have := ih (v / 2) (by omega)
      omega

lemma lt_two_pow_of_le {v w : ℕ} (h : v ≤ w) : v < 2 ^ w :=
  lt_of_le_of_lt h Nat.lt_two_pow_self

/-! ## Layouts -/

/-- Embed a finite type into the first registers. -/
noncomputable def slot (α : Type) [Fintype α] (N : ℕ) (h : Fintype.card α ≤ N) : α ↪ Fin N :=
  ⟨fun a => Fin.castLE h (Fintype.equivFin α a), fun a b hab => by
    simpa using hab⟩

lemma slot_lt {α : Type} [Fintype α] {N : ℕ} {h : Fintype.card α ≤ N} (a : α) :
    (slot α N h a).val < Fintype.card α := by
  show (Fin.castLE h (Fintype.equivFin α a)).val < _
  simp

/-- The number of registers and stacks needed by the simulator of `M`. -/
def need (M : Machine) : ℕ := Fintype.card (Rg (M.tapes + 1)) + Fintype.card (Sk (M.tapes + 1))

/-- Registers of a simulator in a statement with registers `Fin (C + E)`, `need M ≤ C`. -/
noncomputable def ρs (M : Machine) (C E : ℕ) (h : need M ≤ C) : Rg (M.tapes + 1) ↪ Fin (C + E) :=
  slot _ _ (by unfold need at h; omega)

/-- Stacks of a simulator in a statement with stacks `Fin C`, `need M ≤ C`. -/
noncomputable def κs (M : Machine) (C : ℕ) (h : need M ≤ C) : Sk (M.tapes + 1) ↪ Fin C :=
  slot _ _ (by unfold need at h; omega)

/-- The extra register `i`. -/
def ex (C E : ℕ) (i : Fin E) : Fin (C + E) := ⟨C + i, by omega⟩

lemma ρs_ne_ex (M : Machine) {C E : ℕ} (h : need M ≤ C) (g : Rg (M.tapes + 1)) (i : Fin E) :
    ρs M C E h g ≠ ex C E i := by
  intro he
  have := congrArg Fin.val he
  have hl := slot_lt (h := (by unfold need at h; omega : Fintype.card (Rg (M.tapes + 1)) ≤ C + E)) g
  simp only [ρs, ex] at this
  unfold need at h; omega

lemma ex_ne_ex {C E : ℕ} {i j : Fin E} (h : i ≠ j) : ex C E i ≠ ex C E j := by
  intro he; apply h; ext; have := congrArg Fin.val he; simp [ex] at this; omega

/-! ## The simulator in a layout -/

/-- The simulator on a number, in a layout, from a state with all stacks empty. -/
theorem simNat_slot {M : Machine} {C E : ℕ} (h : need M ≤ C) (hw : 2 ≤ w) (hB : simB M ≤ 2 ^ w)
    (st : NSt (C + E) C) (hb : st.Bdd w) (hp : st.pos ≤ x.length) (hemp : ∀ q, st.stk q = [])
    {k v t : ℕ} (hk : st.env (ρs M C E h .inp) = k) (hkw : k < 2 ^ w)
    (hM : ComputesWithin M (encodeNat k) (encodeNat v) t)
    (hs : haltTime M (encodeNat k) < 2 ^ w) (hv : v.bits.length < w) :
    ∃ T, Good x w (simNat M (ρs M C E h) (κs M C h)) st
        (exec x (simNat M (ρs M C E h) (κs M C h)) st) T ∧
      (exec x (simNat M (ρs M C E h) (κs M C h)) st).env (ρs M C E h .out) = v ∧
      (exec x (simNat M (ρs M C E h) (κs M C h)) st).env (ρs M C E h .clk) =
        haltTime M (encodeNat k) ∧
      (∀ q, (exec x (simNat M (ρs M C E h) (κs M C h)) st).stk q = []) ∧
      (∀ i, (exec x (simNat M (ρs M C E h) (κs M C h)) st).env (ex C E i) = st.env (ex C E i)) ∧
      (exec x (simNat M (ρs M C E h) (κs M C h)) st).pos = st.pos ∧
      (exec x (simNat M (ρs M C E h) (κs M C h)) st).out = st.out := by
  obtain ⟨g, e1, e2, e3, e4, e5, e6, e7⟩ := simNat_good (ρs M C E h) (κs M C h) hw hB st hb hp
    (fun g => hemp _) hk hkw hM hs hv
  refine ⟨_, g, e1, e2, fun q => ?_, fun i => e4 _ fun g => ρs_ne_ex M h g i, e6, e7⟩
  by_cases hq : ∃ g, κs M C h g = q
  · obtain ⟨g, rfl⟩ := hq; exact e3 g
  · push Not at hq; rw [e5 q hq, hemp]

end Lax119563Proofs.Computability

end Computability_Bridge

/-! ### Formerly `Lax119563Proofs.Computability.Clock` -/

section Computability_Clock

/-!
# Computable running times

**`MachineComputable.haltTime`**: if a machine `M` computes `f k` from `k` for every `k`, then
its running time `k ↦ haltTime M (encodeNat k)` (the least number of steps after which it has
halted on `encodeNat k`) is computable. The machine computing it simulates `M` with a step
counter (`Computability.simNat`) and outputs the counter.

**`MachineComputable.exists_time`**: every computable function is computed by a machine
whose running time is a computable function.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax119563.DeterministicTime Lax119563.ParameterizedComplexity
open Lax489179.TuringMachine (Machine Config Instruction Move Deterministic)

namespace Lax119563Proofs.Computability

open CStm

variable {w : ℕ}

/-! ## Reading the input number -/

/-- Read the input number into the extra register `0` (scratch: extra registers `1`, `2`). -/
def startS (C E : ℕ) (hE : 3 ≤ E) : CStm (C + E) C :=
  rdNumS (ex C E ⟨0, by omega⟩) (ex C E ⟨1, by omega⟩) (ex C E ⟨2, by omega⟩)

lemma start_good (C E : ℕ) (hE : 3 ≤ E) (hw : 2 ≤ w) (k : ℕ) (hk : k ≤ w - 1) :
    ∃ st T, Good (encodeNat k) w (startS C E hE) (NSt.zero (C + E) C) st T ∧
      st.env (ex C E ⟨0, by omega⟩) = k ∧ (∀ q, st.stk q = []) ∧ st.Bdd w ∧
      st.pos ≤ (encodeNat k).length ∧ st.out = [] := by
  have hn01 : ex C E ⟨0, by omega⟩ ≠ ex C E ⟨1, by omega⟩ := ex_ne_ex (by simp)
  have hn02 : ex C E ⟨0, by omega⟩ ≠ ex C E ⟨2, by omega⟩ := ex_ne_ex (by simp)
  have hn12 : ex C E ⟨1, by omega⟩ ≠ ex C E ⟨2, by omega⟩ := ex_ne_ex (by simp)
  have g := rdNumS_good (x := encodeNat k) (Q := C) hw hn01 hn02 hn12 (NSt.zero (C + E) C) k []
    (by simp [NSt.zero]) (by have := bits_length_le k; omega)
  have hb := CStm.Good.bdd hw g (bdd_zero _ _ _) (by simp [NSt.zero])
  refine ⟨_, _, g, ?_, fun q => by simp [rdNumFinal, NSt.zero], hb.1, hb.2, by
    simp [rdNumFinal, NSt.zero]⟩
  simp [rdNumFinal, Function.update_of_ne hn01, Function.update_of_ne hn02]

/-! ## The clock -/

/-- Output the halting time of `M` on `encodeNat k`, for the input `encodeNat k`. -/
noncomputable def clockS (M : Machine) : CStm (need M + 3) (need M) :=
  seqL [startS (need M) 3 le_rfl,
    .set (ρs M (need M) 3 le_rfl .inp) (.var (ex (need M) 3 ⟨0, by omega⟩)),
    simNat M (ρs M (need M) 3 le_rfl) (κs M (need M) le_rfl),
    .emit (.var (ρs M (need M) 3 le_rfl .clk))]

/-- **Running times are computable.** -/
theorem machineComputable_haltTime {M : Machine} {f : ℕ → ℕ}
    (hM : ∀ k, ∃ t, ComputesWithin M (encodeNat k) (encodeNat (f k)) t) :
    MachineComputable fun k => haltTime M (encodeNat k) := by
  refine machineComputable_of_stm (clockS M) _ fun k => ?_
  obtain ⟨t, ht⟩ := hM k
  set s := Computability.haltTime M (encodeNat k) with hs
  set w := k + s + f k + simB M + 2 with hwdef
  have hw : 2 ≤ w := by omega
  refine ⟨w, hw, ?_⟩
  obtain ⟨st1, T1, g1, e1k, e1s, e1b, e1p, e1o⟩ := start_good (need M) 3 le_rfl hw k (by omega)
  have hkw : k < 2 ^ w := lt_two_pow_of_le (by omega)
  set st2 := st1.set (ρs M (need M) 3 le_rfl .inp) k with hst2
  have g2 : Good (encodeNat k) w (.set (ρs M (need M) 3 le_rfl .inp)
      (.var (ex (need M) 3 ⟨0, by omega⟩)) : CStm (need M + 3) (need M))
      st1 st2 (Ex.nodeCost w + unitCost w) := by
    have e : st2 = st1.set (ρs M (need M) 3 le_rfl .inp)
        ((Ex.var (ex (need M) 3 ⟨0, by omega⟩) : Ex (need M + 3)).eval st1.env) := by
      rw [hst2]; congr 1; simp only [Ex.eval]; exact e1k.symm
    rw [e]
    exact (CStm.Good.set (by simp only [Ex.Fits, e1k]; exact hkw)).mono (by simp [Ex.size])
  have hb2 := CStm.Good.bdd hw g2 e1b (by omega)
  obtain ⟨T3, g3, -, e3c, -, -, -, e3o⟩ := simNat_slot (x := encodeNat k) le_rfl hw
    (lt_two_pow_of_le (by omega)).le st2 hb2.1 hb2.2 (fun q => by simp [hst2, e1s])
    (by simp [hst2]) hkw ht (lt_two_pow_of_le (by omega))
    (by have := bits_length_le (f k); omega)
  set st3 := exec (encodeNat k) (simNat M (ρs M (need M) 3 le_rfl) (κs M (need M) le_rfl)) st2
    with hst3
  have g4 := CStm.Good.emit (x := encodeNat k) (w := w) (st := st3)
    (e := .var (ρs M (need M) 3 le_rfl .clk))
    (by simp only [Ex.Fits]; rw [e3c]; exact lt_two_pow_of_le (by omega))
  refine ⟨_, _, g1.seq (g2.seq (g3.seq (g4.seq CStm.Good.skip))), ?_⟩
  simp [Ex.eval, e3c, e3o, hst2, e1o, hs]

/-- **Computable functions have computable running times.** -/
theorem MachineComputable.exists_time {f : ℕ → ℕ} (hf : MachineComputable f) :
    ∃ M : Machine, Deterministic M ∧
      (∀ k, ComputesWithin M (encodeNat k) (encodeNat (f k))
        (Computability.haltTime M (encodeNat k))) ∧
      MachineComputable fun k => Computability.haltTime M (encodeNat k) := by
  obtain ⟨M, hM, hc⟩ := hf
  refine ⟨M, hM, fun k => ?_, machineComputable_haltTime hc⟩
  obtain ⟨t, ht⟩ := hc k
  exact (ComputesWithin.haltTime ht).1

end Lax119563Proofs.Computability

end Computability_Clock

/-! ### Formerly `Lax119563Proofs.Computability.Call` -/

section Computability_Call

/-!
# Calling a computable function inside a statement

`callS M C E h src`: copy the register `src` into the input register of the simulator of `M`
and run the simulator (`call_good`). Afterwards the output register of the simulator holds
the value computed by `M`, all stacks are empty again, and the extra registers are kept.

`ArithOp H`: a statement computing `H a b` on registers (for large enough word size), with
instances for `+` and `·` (`addOp`, `mulOp`; `^` is `powOp` in `Computability/Closure`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax119563.DeterministicTime Lax119563.ParameterizedComplexity
open Lax489179.TuringMachine (Machine Config Instruction Move Deterministic)

namespace Lax119563Proofs.Computability

open CStm

variable {x : List Bool} {w : ℕ}

/-- Run the simulator of `M` on the value of the register `src`. -/
noncomputable def callS (M : Machine) (C E : ℕ) (h : need M ≤ C) (src : Fin (C + E)) :
    CStm (C + E) C :=
  .seq (.set (ρs M C E h .inp) (.var src)) (simNat M (ρs M C E h) (κs M C h))

theorem call_good {M : Machine} {C E : ℕ} (h : need M ≤ C) (hw : 2 ≤ w) (hB : simB M ≤ 2 ^ w)
    (st : NSt (C + E) C) (hb : st.Bdd w) (hp : st.pos ≤ x.length) (hemp : ∀ q, st.stk q = [])
    (src : Fin (C + E)) {k v t : ℕ} (hk : st.env src = k) (hkw : k < 2 ^ w)
    (hM : ComputesWithin M (encodeNat k) (encodeNat v) t)
    (hs : haltTime M (encodeNat k) < 2 ^ w) (hv : v.bits.length < w) :
    ∃ st' T, Good x w (callS M C E h src) st st' T ∧ st'.env (ρs M C E h .out) = v ∧
      st'.env (ρs M C E h .clk) = haltTime M (encodeNat k) ∧ (∀ q, st'.stk q = []) ∧
      (∀ i, st'.env (ex C E i) = st.env (ex C E i)) ∧ st'.Bdd w ∧ st'.pos = st.pos ∧
      st'.out = st.out := by
  set st1 := st.set (ρs M C E h .inp) k with hst1
  have g1 : Good x w (.set (ρs M C E h .inp) (.var src) : CStm (C + E) C) st st1
      (Ex.nodeCost w + unitCost w) := by
    have e : st1 = st.set (ρs M C E h .inp) ((Ex.var src : Ex (C + E)).eval st.env) := by
      rw [hst1]; congr 1; simp only [Ex.eval]; exact hk.symm
    rw [e]; exact (CStm.Good.set (by simp only [Ex.Fits, hk]; exact hkw)).mono (by simp [Ex.size])
  have hb1 := CStm.Good.bdd hw g1 hb hp
  obtain ⟨T, g2, e1, e2, e3, e4, e5, e6⟩ := simNat_slot (x := x) h hw hB st1 hb1.1 hb1.2
    (fun q => by simp [hst1, hemp]) (by simp [hst1]) hkw hM hs hv
  have g := g1.seq g2
  have hb2 := CStm.Good.bdd hw g hb hp
  refine ⟨_, _, g, e1, e2, e3, fun i => ?_, hb2.1, by rw [e5]; rfl, by rw [e6]; rfl⟩
  rw [e4, hst1, NSt.set_env, Function.update_of_ne (ρs_ne_ex M h _ i).symm]

/-! ## Arithmetic statements -/

/-- A statement computing `H a b` into `o` (scratch registers `s, t, u`), fitting whenever
`W a b ≤ w`. -/
structure ArithOp (H : ℕ → ℕ → ℕ) where
  /-- The statement. -/
  op : {R Q : ℕ} → Fin R → Fin R → Fin R → Fin R → Fin R → Fin R → CStm R Q
  /-- The word size needed. -/
  W : ℕ → ℕ → ℕ
  /-- Correctness. -/
  spec : ∀ {R Q : ℕ} {x : List Bool} {w : ℕ} (a b o s t u : Fin R), [a, b, o, s, t, u].Nodup →
    2 ≤ w → ∀ st : NSt R Q, W (st.env a) (st.env b) ≤ w →
      Fits x w (op a b o s t u) st ∧
      (exec x (op a b o s t u) st).env o = H (st.env a) (st.env b) ∧
      (∀ r, r ≠ o → r ≠ s → r ≠ t → r ≠ u → (exec x (op a b o s t u) st).env r = st.env r) ∧
      (exec x (op a b o s t u) st).stk = st.stk ∧ (exec x (op a b o s t u) st).pos = st.pos ∧
      (exec x (op a b o s t u) st).out = st.out

/-- Addition. -/
def addOp : ArithOp (· + ·) where
  op a b o _ _ _ := .set o (.add (.var a) (.var b))
  W A B := A + B
  spec := fun {R Q x w} a b o s t u hnd hw st hW => by
    refine ⟨?_, by simp [exec, Ex.eval], fun r hr _ _ _ => by simp [exec, Function.update_of_ne hr],
      rfl, rfl, rfl⟩
    simp only [Fits, Ex.Fits, Ex.eval]
    exact ⟨lt_two_pow_of_le (by omega), lt_two_pow_of_le (by omega), lt_two_pow_of_le hW⟩

lemma nodup6 {R : ℕ} {a b o s t u : Fin R} (h : [a, b, o, s, t, u].Nodup) :
    a ≠ b ∧ a ≠ o ∧ a ≠ s ∧ a ≠ t ∧ a ≠ u ∧ b ≠ o ∧ b ≠ s ∧ b ≠ t ∧ b ≠ u ∧ o ≠ s ∧ o ≠ t ∧
      o ≠ u ∧ s ≠ t ∧ s ≠ u ∧ t ≠ u := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h
  tauto

/-- Multiplication. -/
def mulOp : ArithOp (· * ·) where
  op a b o s _ _ := mulS o a b s
  W A B := A * B + B
  spec := fun {R Q x w} a b o s t u hnd hw st hW => by
    obtain ⟨hab, hao, has, -, -, hbo, hbs, -, -, hos, hot, hou, -, -, -⟩ := nodup6 hnd
    have g := mulS_good (x := x) hw hao.symm hbo.symm hos has hbs st rfl rfl
      (lt_two_pow_of_le (by omega)) (lt_two_pow_of_le (by omega))
    rw [g.2.1]
    refine ⟨g.1, by simp [Function.update_of_ne hos], fun r hr hr' _ _ => by
      simp [Function.update_of_ne hr, Function.update_of_ne hr'], rfl, rfl, rfl⟩

end Lax119563Proofs.Computability

end Computability_Call

/-! ### Formerly `Lax119563Proofs.Computability.Closure` -/

section Computability_Closure

/-!
# Closure properties of computable functions

`MachineComputable` contains constants and the identity and is closed under the arithmetic
operations `+`, `·`, `^` (pointwise):

* `MachineComputable.const`, `MachineComputable.id'`;
* `MachineComputable.arith` (any `ArithOp`), `.add`, `.mul`, `.pow`, and the derived
  `.pow_const`, `.add_const`, `.mul_const`.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax119563.DeterministicTime Lax119563.ParameterizedComplexity
open Lax489179.TuringMachine (Machine Config Instruction Move Deterministic)

namespace Lax119563Proofs.Computability

open CStm

variable {x : List Bool} {w : ℕ}

/-! ## Powers -/

/-- `o := a ^ b` (counter `s`, scratch `t`, `u`). -/
def powS {R Q : ℕ} (a b o s t u : Fin R) : CStm R Q :=
  seqL [.set o (.const 1), .set s (.const 0), .loop (.lt (.var s) (.var b))
    (seqL [mulS t o a u, .set o (.var t), .set s (.add (.var s) (.const 1))])]

/-- Powers. -/
def powOp : ArithOp (· ^ ·) where
  op a b o s t u := powS a b o s t u
  W A B := A ^ B + A + B + 2
  spec := fun {R Q x w} a b o s t u hnd hw st hW => by
    obtain ⟨hab, hao, has, hat, hau, hbo, hbs, hbt, hbu, hos, hot, hou, hst, hsu, htu⟩ :=
      nodup6 hnd
    set A := st.env a
    set B := st.env b
    have hpow : ∀ j ≤ B, A ^ j ≤ A ^ B + 1 := fun j hj => by
      rcases Nat.eq_zero_or_pos A with h0 | h0
      · rw [h0]; rcases j with _ | j <;> simp
      · exact (Nat.pow_le_pow_right h0 hj).trans (Nat.le_succ _)
    have hlt : ∀ v, v ≤ A ^ B + A + B + 1 → v < 2 ^ w := fun v hv =>
      lt_two_pow_of_le (by omega)
    set st1 := (st.set o 1).set s 0 with hst1
    set body : CStm R Q := seqL [mulS t o a u, .set o (.var t), .set s (.add (.var s) (.const 1))]
    set S : ℕ → NSt R Q := fun j => iter x body st1 j with hS
    -- one iteration, from any state with the right registers
    have hstep : ∀ (S' : NSt R Q) (j : ℕ), j < B → S'.env o = A ^ j → S'.env s = j →
        S'.env a = A → S'.env b = B →
        Fits x w body S' ∧ exec x body S' =
          (((S'.set t (A ^ j * A)).set u A).set o (A ^ j * A)).set s (j + 1) := by
      intro S' j hj ho hs ha hb
      have hAj : A ^ j * A ≤ A ^ B + 1 := by rw [← pow_succ]; exact hpow _ hj
      have g1 := mulS_good (x := x) hw hot.symm hat.symm htu hou hau S' ho ha
        (hlt (A ^ j * A) (by omega)) (hlt A (by omega))
      set S1 := (S'.set t (A ^ j * A)).set u A with hS1
      have e1t : S1.env t = A ^ j * A := by simp [hS1, Function.update_of_ne htu]
      have e1s : S1.env s = j := by
        simp [hS1, Function.update_of_ne hsu, Function.update_of_ne hst, hs]
      have g2 : Good x w (.set o (.var t) : CStm R Q) S1 (S1.set o (A ^ j * A))
          (Ex.nodeCost w + unitCost w) :=
        (CStm.Good.set (by simp only [Ex.Fits, e1t]; exact hlt _ (by omega))).of_eq
          (by simp [Ex.eval, e1t]) (by simp [Ex.size])
      have e2s : (S1.set o (A ^ j * A)).env s = j := by
        simp [Function.update_of_ne hos.symm, e1s]
      have g3 : Good x w (.set s (.add (.var s) (.const 1)) : CStm R Q) (S1.set o (A ^ j * A))
          ((S1.set o (A ^ j * A)).set s (j + 1)) (3 * Ex.nodeCost w + unitCost w) :=
        (CStm.Good.set (by
          simp only [Ex.Fits, Ex.eval, e2s]
          exact ⟨hlt j (by omega), hlt 1 (by omega), hlt (j + 1) (by omega)⟩)).of_eq
          (by simp [Ex.eval, e2s]) (by simp [Ex.size])
      have g := g1.seq (g2.seq (g3.seq CStm.Good.skip))
      exact ⟨g.1, g.2.1⟩
    have hSj : ∀ j ≤ B, (S j).env o = A ^ j ∧ (S j).env s = j ∧ (S j).env a = A ∧
        (S j).env b = B ∧ (∀ r, r ≠ o → r ≠ s → r ≠ t → r ≠ u → (S j).env r = st.env r) ∧
        (S j).stk = st.stk ∧ (S j).pos = st.pos ∧ (S j).out = st.out := by
      intro j
      induction j with
      | zero =>
        intro _
        simp only [hS, iter_zero, hst1, NSt.set_env, NSt.set_stk, NSt.set_pos, NSt.set_out]
        refine ⟨?_, by simp, ?_, ?_, fun r h1 h2 _ _ => ?_, by simp, by simp, by simp⟩
        · simp [Function.update_of_ne hos]
        · simp [Function.update_of_ne has, Function.update_of_ne hao, A]
        · simp [Function.update_of_ne hbs, Function.update_of_ne hbo, B]
        · simp [Function.update_of_ne h1, Function.update_of_ne h2]
      | succ j ih =>
        intro hj
        obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := ih (by omega)
        rw [show S (j + 1) = exec x body (S j) from iter_succ _ _ _,
          (hstep (S j) j (by omega) i1 i2 i3 i4).2]
        simp only [NSt.set_env, NSt.set_stk, NSt.set_pos, NSt.set_out]
        refine ⟨?_, by simp, ?_, ?_, fun r h1 h2 h3 h4 => ?_, i6, i7, i8⟩
        · rw [Function.update_of_ne hos, Function.update_self, pow_succ]
        · rw [Function.update_of_ne has, Function.update_of_ne hao, Function.update_of_ne hau,
            Function.update_of_ne hat, i3]
        · rw [Function.update_of_ne hbs, Function.update_of_ne hbo, Function.update_of_ne hbu,
            Function.update_of_ne hbt, i4]
        · rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h4,
            Function.update_of_ne h3, i5 r h1 h2 h3 h4]
    have hloop := CStm.Good.loop (x := x) (w := w) (e := .lt (.var s) (.var b)) (body := body) B S
      (fun j => cost x w body (S j))
      (fun j hj => by simp [Ex.eval, (hSj j hj.le).2.1, (hSj j hj.le).2.2.2.1, hj])
      (by simp [Ex.eval, (hSj B le_rfl).2.1, (hSj B le_rfl).2.2.2.1])
      (fun j hj => by
        simp only [Ex.Fits, (hSj j hj).2.1, (hSj j hj).2.2.2.1]
        exact ⟨hlt j (by omega), hlt B (by omega)⟩)
      (fun j hj => by
        obtain ⟨i1, i2, i3, i4, -⟩ := hSj j hj.le
        have := hstep (S j) j hj i1 i2 i3 i4
        rw [show S (j + 1) = exec x body (S j) from iter_succ _ _ _]
        exact ⟨this.1, rfl, le_rfl⟩)
    have g0 := (CStm.Good.set (x := x) (w := w) (r := o) (e := .const 1) (st := st)
      (by simp only [Ex.Fits]; exact hlt 1 (by omega))).seq ((CStm.Good.set (x := x) (w := w) (r := s)
        (e := .const 0) (st := st.set o 1) (by simp [Ex.Fits])).seq (hloop.seq CStm.Good.skip))
    have hex : exec x (powS a b o s t u) st = S B := g0.2.1
    obtain ⟨i1, -, -, -, i5, i6, i7, i8⟩ := hSj B le_rfl
    refine ⟨g0.1, by rw [hex, i1], fun r h1 h2 h3 h4 => by rw [hex, i5 r h1 h2 h3 h4],
      by rw [hex, i6], by rw [hex, i7], by rw [hex, i8]⟩

/-! ## Constants and the identity -/

theorem MachineComputable.const (c : ℕ) : MachineComputable fun _ => c := by
  refine machineComputable_of_stm (.emit (.const c) : CStm 1 0) _ fun k => ⟨c + 2, by omega,
    _, _, CStm.Good.emit (by simp only [Ex.Fits]; exact lt_two_pow_of_le (by omega)), rfl⟩

theorem MachineComputable.id' : MachineComputable fun k => k := by
  refine machineComputable_of_stm (seqL [startS 0 3 le_rfl, .emit (.var (ex 0 3 0))]) _
    fun k => ?_
  obtain ⟨st1, T1, g1, e1k, -, -, -, e1o⟩ := start_good 0 3 le_rfl (w := k + 2) (by omega) k
    (by omega)
  have e1k' : st1.env (ex 0 3 0) = k := e1k
  have hf : (Ex.var (ex 0 3 0) : Ex (0 + 3)).Fits (k + 2) st1.env := by
    simp only [Ex.Fits, e1k']; exact lt_two_pow_of_le (by omega)
  refine ⟨k + 2, by omega, _, _, g1.seq ((CStm.Good.emit hf).seq CStm.Good.skip), ?_⟩
  simp [Ex.eval, e1k', e1o]

/-! ## Composition -/

/-! ## Pointwise arithmetic -/

/-- The statement for `H (f k) (g k)`. -/
noncomputable def arithS {H : ℕ → ℕ → ℕ} (O : ArithOp H) (Mf Mg : Machine) :
    CStm (need Mf + need Mg + 9) (need Mf + need Mg) :=
  seqL [startS _ 9 (by omega), callS Mf _ 9 (by omega) (ex _ 9 0),
    .set (ex _ 9 3) (.var (ρs Mf _ 9 (by omega) .out)),
    callS Mg _ 9 (by omega) (ex _ 9 0),
    .set (ex _ 9 4) (.var (ρs Mg _ 9 (by omega) .out)),
    O.op (ex _ 9 3) (ex _ 9 4) (ex _ 9 5) (ex _ 9 6) (ex _ 9 7) (ex _ 9 8),
    .emit (.var (ex _ 9 5))]

lemma ex_injective (C E : ℕ) : Function.Injective (ex C E) := fun i j h => by
  by_contra hij; exact ex_ne_ex hij h

theorem MachineComputable.arith {H : ℕ → ℕ → ℕ} (O : ArithOp H) {f g : ℕ → ℕ}
    (hf : MachineComputable f) (hg : MachineComputable g) :
    MachineComputable fun k => H (f k) (g k) := by
  obtain ⟨Mf, -, hMf⟩ := hf
  obtain ⟨Mg, -, hMg⟩ := hg
  refine machineComputable_of_stm (arithS O Mf Mg) _ fun k => ?_
  obtain ⟨tf, htf⟩ := hMf k
  obtain ⟨tg, htg⟩ := hMg k
  set C := need Mf + need Mg
  set w := k + haltTime Mf (encodeNat k) + f k + haltTime Mg (encodeNat k) + g k +
    simB Mf + simB Mg + O.W (f k) (g k) + H (f k) (g k) + 2 with hwdef
  have hw : 2 ≤ w := by omega
  refine ⟨w, hw, ?_⟩
  obtain ⟨st1, T1, g1, e1k, e1s, e1b, e1p, e1o⟩ := start_good C 9 (by omega) hw k (by omega)
  obtain ⟨st2, T2, g2, e2o, -, e2s, e2x, e2b, e2p, e2out⟩ := call_good (x := encodeNat k)
    (by omega : need Mf ≤ C) hw (lt_two_pow_of_le (by omega)).le st1 e1b e1p e1s
    (ex _ 9 0) e1k (lt_two_pow_of_le (by omega)) htf (lt_two_pow_of_le (by omega))
    (by have := bits_length_le (f k); omega)
  -- save `f k`
  set st3 := st2.set (ex C 9 3) (f k) with hst3
  have g3 : Good (encodeNat k) w (.set (ex C 9 3) (.var (ρs Mf C 9 (by omega) .out)) :
      CStm (C + 9) C) st2 st3 (Ex.nodeCost w + unitCost w) := by
    have e : st3 = st2.set (ex C 9 3)
        ((Ex.var (ρs Mf C 9 (by omega) .out) : Ex (C + 9)).eval st2.env) := by
      rw [hst3]; congr 1; simp only [Ex.eval]; exact e2o.symm
    rw [e]; exact (CStm.Good.set (by simp only [Ex.Fits, e2o]; exact lt_two_pow_of_le (by omega))).mono
      (by simp [Ex.size])
  have hb3 := CStm.Good.bdd hw g3 e2b (by omega)
  have e3k : st3.env (ex C 9 ⟨0, by omega⟩) = k := by
    rw [hst3, NSt.set_env, Function.update_of_ne (ex_ne_ex (by simp)), e2x, e1k]
  obtain ⟨st4, T4, g4, e4o, -, e4s, e4x, e4b, e4p, e4out⟩ := call_good (x := encodeNat k)
    (by omega : need Mg ≤ C) hw (lt_two_pow_of_le (by omega)).le st3 hb3.1 hb3.2
    (fun q => by simp [hst3, e2s]) (ex _ 9 0) e3k (lt_two_pow_of_le (by omega)) htg
    (lt_two_pow_of_le (by omega)) (by have := bits_length_le (g k); omega)
  -- save `g k`
  set st5 := st4.set (ex C 9 4) (g k) with hst5
  have g5 : Good (encodeNat k) w (.set (ex C 9 4) (.var (ρs Mg C 9 (by omega) .out)) :
      CStm (C + 9) C) st4 st5 (Ex.nodeCost w + unitCost w) := by
    have e : st5 = st4.set (ex C 9 4)
        ((Ex.var (ρs Mg C 9 (by omega) .out) : Ex (C + 9)).eval st4.env) := by
      rw [hst5]; congr 1; simp only [Ex.eval]; exact e4o.symm
    rw [e]; exact (CStm.Good.set (by simp only [Ex.Fits, e4o]; exact lt_two_pow_of_le (by omega))).mono
      (by simp [Ex.size])
  have e5a : st5.env (ex C 9 3) = f k := by
    rw [hst5, NSt.set_env, Function.update_of_ne (ex_ne_ex (by simp)), e4x, hst3]; simp
  have e5b : st5.env (ex C 9 4) = g k := by rw [hst5]; simp
  -- the operation
  have hnd : [ex C 9 3, ex C 9 4, ex C 9 5, ex C 9 6, ex C 9 7, ex C 9 8].Nodup := by
    have : ([3, 4, 5, 6, 7, 8] : List (Fin 9)).Nodup := by decide
    simpa using this.map (ex_injective C 9)
  obtain ⟨o1, o2, -, -, -, o6⟩ := O.spec (x := encodeNat k) (w := w) _ _ _ _ _ _ hnd hw st5
    (by rw [e5a, e5b]; omega)
  set st6 := exec (encodeNat k) (O.op (ex C 9 3) (ex C 9 4) (ex C 9 5) (ex C 9 6) (ex C 9 7)
    (ex C 9 8)) st5 with hst6
  have g6 : Good (encodeNat k) w (O.op (ex C 9 3) (ex C 9 4) (ex C 9 5) (ex C 9 6) (ex C 9 7)
    (ex C 9 8)) st5 st6 _ := ⟨o1, rfl, le_rfl⟩
  rw [e5a, e5b] at o2
  have g7 := CStm.Good.emit (x := encodeNat k) (w := w) (st := st6) (e := .var (ex C 9 5))
    (by simp only [Ex.Fits, o2]; exact lt_two_pow_of_le (by omega))
  refine ⟨_, _, g1.seq (g2.seq (g3.seq (g4.seq (g5.seq (g6.seq (g7.seq CStm.Good.skip)))))), ?_⟩
  simp [Ex.eval, o2, o6, hst5, e4out, hst3, e2out, e1o]

theorem MachineComputable.add {f g : ℕ → ℕ} (hf : MachineComputable f)
    (hg : MachineComputable g) : MachineComputable fun k => f k + g k :=
  MachineComputable.arith addOp hf hg

theorem MachineComputable.mul {f g : ℕ → ℕ} (hf : MachineComputable f)
    (hg : MachineComputable g) : MachineComputable fun k => f k * g k :=
  MachineComputable.arith mulOp hf hg

theorem MachineComputable.pow {f g : ℕ → ℕ} (hf : MachineComputable f)
    (hg : MachineComputable g) : MachineComputable fun k => f k ^ g k :=
  MachineComputable.arith powOp hf hg

theorem MachineComputable.pow_const {f : ℕ → ℕ} (hf : MachineComputable f) (e : ℕ) :
    MachineComputable fun k => f k ^ e :=
  MachineComputable.pow hf (MachineComputable.const e)

theorem MachineComputable.add_const {f : ℕ → ℕ} (hf : MachineComputable f) (b : ℕ) :
    MachineComputable fun k => f k + b :=
  MachineComputable.add hf (MachineComputable.const b)

theorem MachineComputable.mul_const {f : ℕ → ℕ} (hf : MachineComputable f) (a : ℕ) :
    MachineComputable fun k => a * f k :=
  MachineComputable.mul (MachineComputable.const a) hf

end Lax119563Proofs.Computability

end Computability_Closure

/-! ### Formerly `Lax119563Proofs.Computability.Param` -/

section Computability_Param

/-!
# Computing a parameter and a computable function of it inside a statement

For the reductions of parameterized complexity: from the input `x`, compute the parameter
`κ x` (with a machine computing `encodeNat (κ x)` from `x`, e.g. the machine of
`IsParameterized`), then `f (κ x)` for a computable `f` together with the running time of
the machine for `f` on `κ x`.

* `paramS Mκ Mf C E …`: the statement, in the layout with registers `Fin (C + E)` and stacks
  `Fin C`; afterwards the extra registers `0, 1, 2` hold `κ x`, `f (κ x)` and the halting
  time of `Mf` on `encodeNat (κ x)`, all stacks are empty, and the other extra registers
  are kept (`paramS_good`). Further statements can be appended in the same layout.
* The cost is `simInCost Mκ w |x| (haltTime Mκ x) + simNatCost Mf w |encodeNat (κ x)|
  (haltTime Mf (encodeNat (κ x))) + 9 · nodeCost w`, where the two simulator costs are at most
  `simK M · (input length + halting time + 1) · nodeCost w` (`simNatCost_le`, `simInCost_le`).
* `haltTime_le_of_computesWithin`: halting times are bounded by any time bound, e.g. by
  `C (|x| + 1)^d` for the machine of `IsParameterized`; for a computable `f`, the halting time
  of a machine computing `f` is itself computable (`machineComputable_haltTime`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Compiler
open Lax119563.DeterministicTime Lax119563.ParameterizedComplexity
open Lax489179.TuringMachine (Machine Config Instruction Move Deterministic)

namespace Lax119563Proofs.Computability

open CStm

variable {x : List Bool} {w : ℕ}

/-! ## Simplified costs -/

/-- A constant for the cost of simulating `M`. -/
noncomputable def simK (M : Machine) : ℕ :=
  (keys M).length * (8 * (M.tapes + 1) + 12) + 10 * (M.tapes + 1) + 24 *
    (allSk (M.tapes + 1)).length + 250

lemma tailCost_le (M : Machine) (w a s : ℕ) :
    tailCost M w a s + 60 * (a + s + 1) * Ex.nodeCost w ≤ simK M * (a + s + 1) * Ex.nodeCost w := by
  have hU := Ex.unitCost_le_nodeCost w
  unfold tailCost coreCost bodyCost extractCost simK
  generalize (keys M).length * (8 * (M.tapes + 1) + 12) = K1 at *
  generalize (allSk (M.tapes + 1)).length = L at *
  generalize M.tapes + 1 = n at *
  generalize Ex.nodeCost w = N at *
  generalize unitCost w = U at *
  nlinarith [Nat.zero_le (K1 * N * a), Nat.zero_le (n * N * a), Nat.zero_le (L * N * a),
    Nat.zero_le (L * N), Nat.zero_le (N * a), Nat.zero_le (N * s)]

lemma simNatCost_le (M : Machine) (w a s : ℕ) :
    simNatCost M w a s ≤ simK M * (a + s + 1) * Ex.nodeCost w := by
  have := tailCost_le M w a s
  have h : loadNatCost w a ≤ 60 * (a + s + 1) * Ex.nodeCost w := by
    simp only [loadNatCost]; nlinarith
  simp only [simNatCost]; omega

lemma simInCost_le (M : Machine) (w a s : ℕ) :
    simInCost M w a s ≤ simK M * (a + s + 1) * Ex.nodeCost w := by
  have := tailCost_le M w a s
  have h : loadInCost w a ≤ 60 * (a + s + 1) * Ex.nodeCost w := by
    simp only [loadInCost]; nlinarith
  simp only [simInCost]; omega

/-- Halting times are bounded by any time bound. -/
lemma haltTime_le_of_computesWithin {M : Machine} {u y : List Bool} {t : ℕ}
    (h : ComputesWithin M u y t) : haltTime M u ≤ t := (ComputesWithin.haltTime h).2

/-! ## The simulator on the input, in a layout -/

/-- The simulator on the input, in a layout, from a state with all stacks empty. -/
theorem simIn_slot {M : Machine} {C E : ℕ} (h : need M ≤ C) (hw : 2 ≤ w) (hB : simB M ≤ 2 ^ w)
    (st : NSt (C + E) C) (hb : st.Bdd w) (hp : st.pos ≤ x.length) (hemp : ∀ q, st.stk q = [])
    {v t : ℕ} (hM : ComputesWithin M x (encodeNat v) t)
    (hs : haltTime M x < 2 ^ w) (hv : v.bits.length < w) :
    Good x w (simIn M (ρs M C E h) (κs M C h)) st (exec x (simIn M (ρs M C E h) (κs M C h)) st)
        (simInCost M w x.length (haltTime M x)) ∧
      (exec x (simIn M (ρs M C E h) (κs M C h)) st).env (ρs M C E h .out) = v ∧
      (∀ q, (exec x (simIn M (ρs M C E h) (κs M C h)) st).stk q = []) ∧
      (∀ i, (exec x (simIn M (ρs M C E h) (κs M C h)) st).env (ex C E i) = st.env (ex C E i)) ∧
      (exec x (simIn M (ρs M C E h) (κs M C h)) st).pos = x.length ∧
      (exec x (simIn M (ρs M C E h) (κs M C h)) st).out = st.out := by
  obtain ⟨g, e1, -, e3, e4, e5, e6, e7⟩ := simIn_good (ρs M C E h) (κs M C h) hw hB st hb hp
    (fun g => hemp _) hM hs hv
  refine ⟨g, e1, fun q => ?_, fun i => e4 _ fun g => ρs_ne_ex M h g i, e6, e7⟩
  by_cases hq : ∃ g, κs M C h g = q
  · obtain ⟨g, rfl⟩ := hq; exact e3 g
  · push Not at hq; rw [e5 q hq, hemp]

/-- The cost of a call. -/
theorem call_cost {M : Machine} {C E : ℕ} (h : need M ≤ C) (hw : 2 ≤ w) (hB : simB M ≤ 2 ^ w)
    (st : NSt (C + E) C) (hb : st.Bdd w) (hp : st.pos ≤ x.length) (hemp : ∀ q, st.stk q = [])
    (src : Fin (C + E)) {k v t : ℕ} (hk : st.env src = k) (hkw : k < 2 ^ w)
    (hM : ComputesWithin M (encodeNat k) (encodeNat v) t)
    (hs : haltTime M (encodeNat k) < 2 ^ w) (hv : v.bits.length < w) :
    Good x w (callS M C E h src) st (exec x (callS M C E h src) st)
      (Ex.nodeCost w + unitCost w + simNatCost M w (encodeNat k).length
        (haltTime M (encodeNat k))) := by
  set st1 := st.set (ρs M C E h .inp) k with hst1
  have g1 : Good x w (.set (ρs M C E h .inp) (.var src) : CStm (C + E) C) st st1
      (Ex.nodeCost w + unitCost w) := by
    have e : st1 = st.set (ρs M C E h .inp) ((Ex.var src : Ex (C + E)).eval st.env) := by
      rw [hst1]; congr 1; simp only [Ex.eval]; exact hk.symm
    rw [e]; exact (CStm.Good.set (by simp only [Ex.Fits, hk]; exact hkw)).mono (by simp [Ex.size])
  have hb1 := CStm.Good.bdd hw g1 hb hp
  have g2 := (simNat_good (ρs M C E h) (κs M C h) hw hB st1 hb1.1 hb1.2
    (fun g => by simp [hst1, hemp]) (by simp [hst1]) hkw hM hs hv).1
  have g := g1.seq g2
  have e : exec x (callS M C E h src) st = _ := g.2.1
  rw [e]; exact g

/-! ## The parameter and a function of it -/

/-- Compute `κ x` (machine `Mκ`) into the extra register `0`, then `f (κ x)` (machine `Mf`)
into the extra register `1` and the halting time of `Mf` into the extra register `2`. -/
noncomputable def paramS (Mκ Mf : Machine) (C E : ℕ) (hκ : need Mκ ≤ C) (hf : need Mf ≤ C)
    (hE : 3 ≤ E) : CStm (C + E) C :=
  seqL [simIn Mκ (ρs Mκ C E hκ) (κs Mκ C hκ),
    .set (ex C E ⟨0, by omega⟩) (.var (ρs Mκ C E hκ .out)),
    callS Mf C E hf (ex C E ⟨0, by omega⟩),
    .set (ex C E ⟨1, by omega⟩) (.var (ρs Mf C E hf .out)),
    .set (ex C E ⟨2, by omega⟩) (.var (ρs Mf C E hf .clk))]

/-- **Computing the parameter and a computable function of it.** -/
theorem paramS_good {Mκ Mf : Machine} {C E : ℕ} (hκ : need Mκ ≤ C) (hf : need Mf ≤ C)
    (hE : 3 ≤ E) (hw : 2 ≤ w) (hBκ : simB Mκ ≤ 2 ^ w) (hBf : simB Mf ≤ 2 ^ w)
    (st : NSt (C + E) C) (hb : st.Bdd w) (hp : st.pos ≤ x.length) (hemp : ∀ q, st.stk q = [])
    {k v tκ tf : ℕ} (hMκ : ComputesWithin Mκ x (encodeNat k) tκ)
    (hMf : ComputesWithin Mf (encodeNat k) (encodeNat v) tf)
    (hsκ : haltTime Mκ x < 2 ^ w) (hk : k.bits.length < w) (hkw : k < 2 ^ w)
    (hsf : haltTime Mf (encodeNat k) < 2 ^ w) (hv : v.bits.length < w) (hvw : v < 2 ^ w) :
    ∃ st', Good x w (paramS Mκ Mf C E hκ hf hE) st st'
        (simInCost Mκ w x.length (haltTime Mκ x) +
          simNatCost Mf w (encodeNat k).length (haltTime Mf (encodeNat k)) +
          9 * Ex.nodeCost w) ∧
      st'.env (ex C E ⟨0, by omega⟩) = k ∧ st'.env (ex C E ⟨1, by omega⟩) = v ∧
      st'.env (ex C E ⟨2, by omega⟩) = haltTime Mf (encodeNat k) ∧
      (∀ i : Fin E, 3 ≤ i.val → st'.env (ex C E i) = st.env (ex C E i)) ∧
      (∀ q, st'.stk q = []) ∧ st'.Bdd w ∧ st'.pos = x.length ∧ st'.out = st.out := by
  have hU := Ex.unitCost_le_nodeCost w
  obtain ⟨g1, e1o, e1s, e1x, e1p, e1out⟩ := simIn_slot (x := x) hκ hw hBκ st hb hp hemp hMκ hsκ hk
  set st1 := exec x (simIn Mκ (ρs Mκ C E hκ) (κs Mκ C hκ)) st with hst1
  set st2 := st1.set (ex C E ⟨0, by omega⟩) k with hst2
  have g2 : Good x w (.set (ex C E ⟨0, by omega⟩) (.var (ρs Mκ C E hκ .out)) : CStm (C + E) C)
      st1 st2 (Ex.nodeCost w + unitCost w) :=
    (CStm.Good.set (by simp only [Ex.Fits, e1o]; exact hkw)).of_eq (by simp [hst2, Ex.eval, e1o])
      (by simp [Ex.size])
  have hb2 := CStm.Good.bdd hw (g1.seq g2) hb hp
  obtain ⟨st3, T3, g3, e3o, e3c, e3s, e3x, e3b, e3p, e3out⟩ := call_good (x := x) hf hw hBf st2
    hb2.1 hb2.2 (fun q => by simp [hst2, e1s]) (ex C E ⟨0, by omega⟩) (by simp [hst2]) hkw hMf
    hsf hv
  set st4 := st3.set (ex C E ⟨1, by omega⟩) v with hst4
  have g4 : Good x w (.set (ex C E ⟨1, by omega⟩) (.var (ρs Mf C E hf .out)) : CStm (C + E) C)
      st3 st4 (Ex.nodeCost w + unitCost w) :=
    (CStm.Good.set (by simp only [Ex.Fits, e3o]; exact hvw)).of_eq (by simp [hst4, Ex.eval, e3o])
      (by simp [Ex.size])
  have e4c : st4.env (ρs Mf C E hf .clk) = haltTime Mf (encodeNat k) := by
    rw [hst4, NSt.set_env, Function.update_of_ne (ρs_ne_ex Mf hf _ _), e3c]
  set st5 := st4.set (ex C E ⟨2, by omega⟩) (haltTime Mf (encodeNat k)) with hst5
  have g5 : Good x w (.set (ex C E ⟨2, by omega⟩) (.var (ρs Mf C E hf .clk)) : CStm (C + E) C)
      st4 st5 (Ex.nodeCost w + unitCost w) :=
    (CStm.Good.set (by simp only [Ex.Fits, e4c]; exact hsf)).of_eq (by simp [hst5, Ex.eval, e4c])
      (by simp [Ex.size])
  have g3' : Good x w (callS Mf C E hf (ex C E ⟨0, by omega⟩)) st2 st3
      (Ex.nodeCost w + unitCost w + simNatCost Mf w (encodeNat k).length
        (haltTime Mf (encodeNat k))) := by
    have := call_cost (x := x) hf hw hBf st2 hb2.1 hb2.2 (fun q => by simp [hst2, e1s])
      (ex C E ⟨0, by omega⟩) (by simp [hst2]) hkw hMf hsf hv
    rwa [g3.2.1] at this
  have g : Good x w (paramS Mκ Mf C E hκ hf hE) st st5 _ :=
    g1.seq (g2.seq (g3'.seq (g4.seq (g5.seq CStm.Good.skip))))
  have hbd := CStm.Good.bdd hw g hb hp
  refine ⟨st5, g.mono (by omega), ?_, ?_, by simp [hst5], fun i hi => ?_, fun q => by
    simp [hst5, hst4, e3s], hbd.1, by simp [hst5, hst4, e3p, hst2, e1p], by
    simp [hst5, hst4, e3out, hst2, e1out]⟩
  · rw [hst5, NSt.set_env, Function.update_of_ne (ex_ne_ex (by simp)), hst4, NSt.set_env,
      Function.update_of_ne (ex_ne_ex (by simp)), e3x, hst2]; simp
  · rw [hst5, NSt.set_env, Function.update_of_ne (ex_ne_ex (by simp)), hst4]; simp
  · have h0 : i ≠ ⟨0, by omega⟩ := fun h => by rw [h] at hi; simp at hi
    have h1 : i ≠ ⟨1, by omega⟩ := fun h => by rw [h] at hi; simp at hi
    have h2 : i ≠ ⟨2, by omega⟩ := fun h => by rw [h] at hi; simp at hi
    rw [hst5, NSt.set_env, Function.update_of_ne (ex_ne_ex h2), hst4, NSt.set_env,
      Function.update_of_ne (ex_ne_ex h1), e3x, hst2, NSt.set_env,
      Function.update_of_ne (ex_ne_ex h0), e1x]

end Lax119563Proofs.Computability

end Computability_Param

/-! ### Formerly `Lax119563Proofs.Hardness.PrefixProgram` -/

section Hardness_PrefixProgram

/-!
# Computing the parameters of the exponential lower bound

For a constant `c₀`, the structured program `parProg c₀` reads its input `x`, counts its
length `n`, computes `a = ⌈log₂ (n + 2)⌉` (`parA n`) by repeated doubling and
`s = ⌊(n + c₀ + 1) / a⌋ + 1` (`parS c₀ n`, the least `s` with `s a ≥ n + c₀ + 2`) by repeated
addition, and emits `[n + c₀, s]`. Its machine computes `encodeNats [n + c₀, s]` from `x`
within `K (n + 1)^3` steps (`parMachine_computesWithin`).
-/

open Lax119563.BinaryEncodings Lax119563.DeterministicTime Lax119563Proofs.Reduction
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Hardness

open Compiler Compiler.CStm

/-- `⌈log₂ (n + 2)⌉`. -/
def parA (n : ℕ) : ℕ := Nat.clog 2 (n + 2)

/-- The number of data blocks: the least `s` with `s · parA n ≥ n + c₀ + 2`. -/
def parS (c₀ n : ℕ) : ℕ := (n + c₀ + 1) / parA n + 1

lemma one_le_parA (n : ℕ) : 1 ≤ parA n := Nat.clog_pos (by norm_num) (by omega)

lemma le_pow_parA (n : ℕ) : n + 2 ≤ 2 ^ parA n := Nat.le_pow_clog (by norm_num) _

lemma pow_parA_le (n : ℕ) : 2 ^ parA n ≤ 2 * (n + 2) := by
  have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := n + 2) (by omega)
  have h1 := one_le_parA n
  unfold parA at h1 ⊢
  obtain ⟨k, hk⟩ : ∃ k, Nat.clog 2 (n + 2) = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h1).symm⟩
  rw [hk] at h ⊢
  simp only [Nat.pred_succ] at h
  rw [pow_succ]; omega

lemma parA_le (n : ℕ) : parA n ≤ n + 2 :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

lemma pow_lt_of_lt_parA {n j : ℕ} (hj : j < parA n) : 2 ^ j < n + 2 :=
  (Nat.lt_clog_iff_pow_lt (by norm_num)).mp hj

lemma one_le_parS (c₀ n : ℕ) : 1 ≤ parS c₀ n := Nat.le_add_left 1 _

lemma parS_spec (c₀ n : ℕ) :
    n + c₀ + 2 ≤ parS c₀ n * parA n ∧ ∀ j < parS c₀ n, j * parA n < n + c₀ + 2 := by
  have ha := one_le_parA n
  refine ⟨?_, fun j hj => ?_⟩
  · unfold parS
    have := Nat.lt_div_mul_add (a := n + c₀ + 1) ha
    rw [add_mul, one_mul]; omega
  · unfold parS at hj
    have hj' : j ≤ (n + c₀ + 1) / parA n := by omega
    have := (Nat.le_div_iff_mul_le ha).mp hj'
    omega

/-! ## The program -/

/-- States of the program: registers `b, n, p, a, acc, s`. -/
def st6 (b n p a c s pos : ℕ) (out : List ℕ) : NSt 6 0 :=
  ⟨![b, n, p, a, c, s], fun _ => [], pos, out⟩

/-- The program. -/
def parProg (c₀ : ℕ) : CStm 6 0 :=
  .seq (.seq (.rd 0) (.loop (.var 0) (.seq (.set 1 (.add (.var 1) (.const 1))) (.rd 0))))
  (.seq (.seq (.set 2 (.const 1)) (.loop (.lt (.var 2) (.add (.var 1) (.const 2)))
      (.seq (.set 2 (.add (.var 2) (.var 2))) (.set 3 (.add (.var 3) (.const 1))))))
  (.seq (.loop (.lt (.var 4) (.add (.var 1) (.const (c₀ + 2))))
      (.seq (.set 4 (.add (.var 4) (.var 3))) (.set 5 (.add (.var 5) (.const 1)))))
  (.seq (.emit (.add (.var 1) (.const c₀))) (.emit (.var 5)))))

lemma parProg_depth (c₀ : ℕ) : (parProg c₀).depth ≤ 10 := by
  simp [parProg, CStm.depth, Ex.depth]

lemma inBit_lt {x : List Bool} {j : ℕ} (hj : j < x.length) : inBit x j ≠ 0 := by
  rw [inBit_eqN, List.drop_eq_getElem_cons hj]
  simp [rdVal]

lemma inBit_len (x : List Bool) : inBit x x.length = 0 := by
  rw [inBit_eqN]; simp [rdVal]

lemma inBit_le' (x : List Bool) (pos : ℕ) : inBit x pos ≤ 2 := by
  rw [inBit_eqN]
  rcases x.drop pos with _ | ⟨b, _⟩
  · simp [rdVal]
  · cases b <;> simp [rdVal]

section Good

variable {x : List Bool} {w : ℕ}

/-- Abbreviation of the cost of an expression node. -/
local notation "NC" => Ex.nodeCost w

lemma unit_le_nc : unitCost w ≤ NC := Ex.unitCost_le_nodeCost w

lemma cond_le (e : Ex 6) (hs : e.size ≤ 5) : condCost w e ≤ 6 * NC := by
  unfold condCost
  have : 1 ≤ unitCost w := by unfold unitCost; omega
  have := @unit_le_nc w
  calc e.size * NC + 1 ≤ 5 * NC + NC := by gcongr; omega
    _ = 6 * NC := by ring

/-- Phase 1: reading the input. -/
lemma good_phase1 (hw2 : 2 ≤ w) (hw : x.length + 3 < 2 ^ w) :
    Good x w (.seq (.rd 0) (.loop (.var 0) (.seq (.set 1 (.add (.var 1) (.const 1))) (.rd 0))))
      (NSt.zero 6 0) (st6 0 x.length 0 0 0 0 x.length []) ((x.length + 1) * (20 * NC)) := by
  have h1 : Good x w (.rd 0 : CStm 6 0) (NSt.zero 6 0) (st6 (inBit x 0) 0 0 0 0 0 (min 1 x.length) [])
      (unitCost w) := by
    refine (CStm.Good.rd 0).of_eq ?_ le_rfl
    refine NSt.ext (funext fun i => ?_) (funext fun i => i.elim0) rfl rfl
    fin_cases i <;> simp [NSt.zero, st6]
  have hS : ∀ j < x.length, Good x w (.seq (.set 1 (.add (.var 1) (.const 1))) (.rd 0) : CStm 6 0)
      (st6 (inBit x j) j 0 0 0 0 (min (j + 1) x.length) [])
      (st6 (inBit x (j + 1)) (j + 1) 0 0 0 0 (min (j + 1 + 1) x.length) []) (8 * NC) := by
    intro j hj
    have hf : (Ex.add (.var 1) (.const 1) : Ex 6).Fits w
        (st6 (inBit x j) j 0 0 0 0 (min (j + 1) x.length) []).env := by
      simp [Ex.Fits, st6, Ex.eval]
      omega
    refine ((CStm.Good.set hf).seq (CStm.Good.rd 0)).of_eq ?_ ?_
    · refine NSt.ext (funext fun i => ?_) rfl ?_ rfl
      · fin_cases i <;> simp [st6, Ex.eval, Function.update, show min (j + 1) x.length = j + 1 by omega]
      · simp [st6]; omega
    · simp only [Ex.size]
      have := @unit_le_nc w
      omega
  have hl := CStm.Good.loop_const (x := x) (w := w) (e := (.var 0 : Ex 6)) x.length
    (fun j => st6 (inBit x j) j 0 0 0 0 (min (j + 1) x.length) []) (8 * NC)
    (fun j hj => by simpa [st6, Ex.eval] using inBit_lt hj)
    (by simpa [st6, Ex.eval] using inBit_len x)
    (fun j hj => by
      have := inBit_le' x j
      simp [Ex.Fits, st6]; omega)
    hS
  refine (h1.seq (hl.of_eq ?_ le_rfl)).of_eq rfl ?_
  · simp [st6, inBit_len]
  · have := cond_le (w := w) (.var 0) (by simp [Ex.size])
    have := @unit_le_nc w
    have e : (x.length + 1) * (20 * NC) = x.length * (20 * NC) + 20 * NC := by ring
    have e2 : x.length * (8 * NC + condCost w (.var 0 : Ex 6)) ≤ x.length * (20 * NC) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

/-- Phase 2: `a = ⌈log₂ (n + 2)⌉` by doubling. -/
lemma good_phase2 (n : ℕ) (hw2 : 2 ≤ w) (hw : 4 * (n + 4) < 2 ^ w) :
    Good x w (.seq (.set 2 (.const 1)) (.loop (.lt (.var 2) (.add (.var 1) (.const 2)))
      (.seq (.set 2 (.add (.var 2) (.var 2))) (.set 3 (.add (.var 3) (.const 1))))))
      (st6 0 n 0 0 0 0 n []) (st6 0 n (2 ^ parA n) (parA n) 0 0 n [])
      ((parA n + 1) * (20 * NC)) := by
  have hA := pow_parA_le n
  have h1 : Good x w (.set 2 (.const 1) : CStm 6 0) (st6 0 n 0 0 0 0 n [])
      (st6 0 n (2 ^ 0) 0 0 0 n []) (2 * NC) := by
    refine (CStm.Good.set (by simp [Ex.Fits]; omega)).of_eq ?_ ?_
    · refine NSt.ext (funext fun i => ?_) rfl rfl rfl
      fin_cases i <;> simp [st6, Ex.eval]
    · simp only [Ex.size]; have := @unit_le_nc w; omega
  have hS : ∀ j < parA n, Good x w
      (.seq (.set 2 (.add (.var 2) (.var 2))) (.set 3 (.add (.var 3) (.const 1))) : CStm 6 0)
      (st6 0 n (2 ^ j) j 0 0 n []) (st6 0 n (2 ^ (j + 1)) (j + 1) 0 0 n []) (8 * NC) := by
    intro j hj
    have hj2 : 2 ^ (j + 1) ≤ 2 ^ parA n := Nat.pow_le_pow_right (by norm_num) hj
    have hja : j + 1 ≤ n + 2 := by have := parA_le n; omega
    rw [pow_succ] at hj2
    have hf1 : (Ex.add (.var 2) (.var 2) : Ex 6).Fits w (st6 0 n (2 ^ j) j 0 0 n []).env := by
      simp [Ex.Fits, st6, Ex.eval]; omega
    have hf2 : (Ex.add (.var 3) (.const 1) : Ex 6).Fits w
        ((st6 0 n (2 ^ j) j 0 0 n []).set 2 (2 ^ j + 2 ^ j)).env := by
      simp [Ex.Fits, st6, Ex.eval, Function.update]; omega
    refine ((CStm.Good.set hf1).seq (CStm.Good.set hf2)).of_eq ?_ ?_
    · refine NSt.ext (funext fun i => ?_) rfl rfl rfl
      fin_cases i <;> simp [st6, Ex.eval, Function.update, pow_succ] <;> ring
    · simp only [Ex.size]; have := @unit_le_nc w; omega
  have hl := CStm.Good.loop_const (x := x) (w := w)
    (e := (.lt (.var 2) (.add (.var 1) (.const 2)) : Ex 6)) (parA n)
    (fun j => st6 0 n (2 ^ j) j 0 0 n []) (8 * NC)
    (fun j hj => by simp [st6, Ex.eval, pow_lt_of_lt_parA hj])
    (by simp [st6, Ex.eval, not_lt.mpr (le_pow_parA n)])
    (fun j hj => by
      have : 2 ^ j ≤ 2 ^ parA n := Nat.pow_le_pow_right (by norm_num) hj
      simp [Ex.Fits, st6, Ex.eval]; omega)
    hS
  refine (h1.seq hl).mono ?_
  have := cond_le (w := w) (.lt (.var 2) (.add (.var 1) (.const 2))) (by simp [Ex.size])
  have e : (parA n + 1) * (20 * NC) = parA n * (20 * NC) + 20 * NC := by ring
  have e2 : parA n * (8 * NC + condCost w (.lt (.var 2) (.add (.var 1) (.const 2)) : Ex 6)) ≤
      parA n * (20 * NC) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- Phase 3: `s` by repeated addition. -/
lemma good_phase3 (c₀ n : ℕ) (hw2 : 2 ≤ w) (hw : 4 * (n + c₀ + 4) < 2 ^ w) :
    Good x w (.loop (.lt (.var 4) (.add (.var 1) (.const (c₀ + 2))))
      (.seq (.set 4 (.add (.var 4) (.var 3))) (.set 5 (.add (.var 5) (.const 1)))))
      (st6 0 n (2 ^ parA n) (parA n) (0 * parA n) 0 n [])
      (st6 0 n (2 ^ parA n) (parA n) (parS c₀ n * parA n) (parS c₀ n) n [])
      ((parS c₀ n + 1) * (20 * NC)) := by
  obtain ⟨hs1, hs2⟩ := parS_spec c₀ n
  have ha := parA_le n
  have hsa : parS c₀ n * parA n ≤ n + c₀ + 2 + parA n := by
    have := hs2 (parS c₀ n - 1) (by have := one_le_parS c₀ n; omega)
    have e : parS c₀ n * parA n = (parS c₀ n - 1) * parA n + parA n := by
      have : 1 ≤ parS c₀ n := one_le_parS c₀ n
      obtain ⟨k, hk⟩ : ∃ k, parS c₀ n = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos this).symm⟩
      rw [hk]; simp; ring
    omega
  have hsle : parS c₀ n ≤ n + c₀ + 2 := by
    have := hs2 (parS c₀ n - 1) (by have := one_le_parS c₀ n; omega)
    have h1 := one_le_parA n
    have : parS c₀ n - 1 ≤ (parS c₀ n - 1) * parA n := Nat.le_mul_of_pos_right _ h1
    omega
  have hS : ∀ j < parS c₀ n, Good x w
      (.seq (.set 4 (.add (.var 4) (.var 3))) (.set 5 (.add (.var 5) (.const 1))) : CStm 6 0)
      (st6 0 n (2 ^ parA n) (parA n) (j * parA n) j n [])
      (st6 0 n (2 ^ parA n) (parA n) ((j + 1) * parA n) (j + 1) n []) (8 * NC) := by
    intro j hj
    have hj' := hs2 j hj
    have hf1 : (Ex.add (.var 4) (.var 3) : Ex 6).Fits w
        (st6 0 n (2 ^ parA n) (parA n) (j * parA n) j n []).env := by
      simp [Ex.Fits, st6, Ex.eval]; omega
    have hf2 : (Ex.add (.var 5) (.const 1) : Ex 6).Fits w
        ((st6 0 n (2 ^ parA n) (parA n) (j * parA n) j n []).set 4
          (j * parA n + parA n)).env := by
      simp [Ex.Fits, st6, Ex.eval, Function.update]; omega
    refine ((CStm.Good.set hf1).seq (CStm.Good.set hf2)).of_eq ?_ ?_
    · refine NSt.ext (funext fun i => ?_) rfl rfl rfl
      fin_cases i <;> simp [st6, Ex.eval, Function.update] <;> ring
    · simp only [Ex.size]; have := @unit_le_nc w; omega
  have hl := CStm.Good.loop_const (x := x) (w := w)
    (e := (Ex.lt (.var 4) (.add (.var 1) (.const (c₀ + 2))))) (parS c₀ n)
    (fun j => st6 0 n (2 ^ parA n) (parA n) (j * parA n) j n []) (8 * NC)
    (fun j hj => by
      have := hs2 j hj
      simp [st6, Ex.eval, show j * parA n < n + (c₀ + 2) by omega])
    (by simp [st6, Ex.eval, not_lt.mpr (show n + (c₀ + 2) ≤ parS c₀ n * parA n by omega)])
    (fun j hj => by
      have : j * parA n ≤ parS c₀ n * parA n := Nat.mul_le_mul_right _ hj
      simp [Ex.Fits, st6, Ex.eval]; omega)
    hS
  refine hl.mono ?_
  have := cond_le (w := w) (.lt (.var 4) (.add (.var 1) (.const (c₀ + 2)))) (by simp [Ex.size])
  have e : (parS c₀ n + 1) * (20 * NC) = parS c₀ n * (20 * NC) + 20 * NC := by ring
  have e2 : parS c₀ n * (8 * NC +
      condCost w (Ex.lt (.var 4) (.add (.var 1) (.const (c₀ + 2))))) ≤
      parS c₀ n * (20 * NC) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- Phase 4: the output. -/
lemma good_phase4 (c₀ n p a c s : ℕ) (hw : n + c₀ + s < 2 ^ w) :
    Good x w (.seq (.emit (.add (.var 1) (.const c₀))) (.emit (.var 5)) : CStm 6 0)
      (st6 0 n p a c s n []) (st6 0 n p a c s n [n + c₀, s]) (8 * NC) := by
  refine ((CStm.Good.emit (by simp [Ex.Fits, st6, Ex.eval]; omega)).seq
    (CStm.Good.emit (by simp [Ex.Fits, st6]; omega))).of_eq ?_ ?_
  · simp [st6, Ex.eval]
  · simp only [Ex.size]; have := @unit_le_nc w; omega

/-- **The program.** -/
lemma good_parProg (c₀ : ℕ) (hw2 : 2 ≤ w) (hw : 4 * (x.length + c₀ + 4) < 2 ^ w) :
    Good x w (parProg c₀) (NSt.zero 6 0)
      (st6 0 x.length (2 ^ parA x.length) (parA x.length) (parS c₀ x.length * parA x.length)
        (parS c₀ x.length) x.length [x.length + c₀, parS c₀ x.length])
      (100 * (x.length + c₀ + 4) * NC) := by
  have h1 := good_phase1 (x := x) hw2 (by omega)
  have h2 := good_phase2 (x := x) x.length hw2 (by omega)
  have h3 := good_phase3 (x := x) c₀ x.length hw2 hw
  have hsle : parS c₀ x.length ≤ x.length + c₀ + 2 := by
    obtain ⟨-, hs2⟩ := parS_spec c₀ x.length
    have := hs2 (parS c₀ x.length - 1)
      (by have := one_le_parS c₀ x.length; omega)
    have h1 := one_le_parA x.length
    have : parS c₀ x.length - 1 ≤ (parS c₀ x.length - 1) * parA x.length :=
      Nat.le_mul_of_pos_right _ h1
    omega
  have h4 := good_phase4 (x := x) (w := w) c₀ x.length (2 ^ parA x.length) (parA x.length)
    (parS c₀ x.length * parA x.length) (parS c₀ x.length) (by omega)
  rw [show (st6 0 x.length (2 ^ parA x.length) (parA x.length) 0 0 x.length [] : NSt 6 0) =
    st6 0 x.length (2 ^ parA x.length) (parA x.length) (0 * parA x.length) 0 x.length [] by
      simp] at h2
  refine (h1.seq (h2.seq (h3.seq h4))).mono ?_
  have ha := parA_le x.length
  have e1 : (x.length + 1) * (20 * NC) + ((parA x.length + 1) * (20 * NC) +
      ((parS c₀ x.length + 1) * (20 * NC) + 8 * NC)) =
      (x.length + parA x.length + parS c₀ x.length + 3) * (20 * NC) + 8 * NC := by ring
  have e2 : (x.length + parA x.length + parS c₀ x.length + 3) * (20 * NC) ≤
      (3 * (x.length + c₀ + 4)) * (20 * NC) := Nat.mul_le_mul_right _ (by omega)
  have e3 : 100 * (x.length + c₀ + 4) * NC = (3 * (x.length + c₀ + 4)) * (20 * NC) +
      (40 * (x.length + c₀ + 4)) * NC := by ring
  have e4 : 8 * NC ≤ (40 * (x.length + c₀ + 4)) * NC := Nat.mul_le_mul_right _ (by omega)
  omega

end Good

end Lax119563Proofs.Hardness

end Hardness_PrefixProgram

/-! ### Formerly `Lax119563Proofs.Hardness.ParMachine` -/

section Hardness_ParMachine

/-!
# The machine putting the parameters in front of the input

For a constant `c₀` there is a deterministic machine that computes
`encodeNats [n + c₀, parS c₀ n] ++ x` from an input `x` of length `n` within
`K (n + c₀ + 4)^3` steps (`par_machine`): the machine of `parProg c₀` followed by
`withSuffix`.
-/

open Lax119563.BinaryEncodings Lax119563.DeterministicTime Lax119563Proofs.Reduction
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Hardness

open Compiler Compiler.CStm

lemma nodeCost_le (m : ℕ) (hm : 1 ≤ m) : Ex.nodeCost (4 * m) ≤ 64 * 49 * m ^ 2 := by
  unfold Ex.nodeCost unitCost
  have h1 : 4 * m + 3 ≤ 7 * m := by omega
  have h2 : 4 * m + 1 ≤ 7 * m := by omega
  calc (4 * m + 3) * (64 * (4 * m + 1)) ≤ (7 * m) * (64 * (7 * m)) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul_left _ h2)
    _ = 64 * 49 * m ^ 2 := by ring

lemma par_time_arith {m n c₀ s cost : ℕ} (hm : m = n + c₀ + 4) (hs : s ≤ n + c₀ + 2)
    (hcost : cost ≤ 100 * m * Ex.nodeCost (4 * m)) :
    16 * (cost + 20 * (n + ((2 * (n + c₀) + 1) + (2 * s + 1))) + 10 + n + 1) ≤
      16 * (100 * 64 * 49 + 200) * m ^ 3 := by
  have hm1 : 1 ≤ m := by omega
  have hN := nodeCost_le m hm1
  have h1 : cost ≤ 100 * 64 * 49 * m ^ 3 := by
    calc cost ≤ 100 * m * (64 * 49 * m ^ 2) := hcost.trans (Nat.mul_le_mul_left _ hN)
      _ = 100 * 64 * 49 * m ^ 3 := by ring
  have h2 : m ≤ m ^ 3 := by
    calc m = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ 3 := Nat.pow_le_pow_right hm1 (by norm_num)
  have e : 16 * (100 * 64 * 49 + 200) * m ^ 3 = 16 * (100 * 64 * 49 * m ^ 3 + 200 * m ^ 3) := by
    ring
  omega

lemma parS_le (c₀ n : ℕ) : parS c₀ n ≤ n + c₀ + 2 := by
  obtain ⟨-, hs2⟩ := parS_spec c₀ n
  have := hs2 (parS c₀ n - 1) (by have := one_le_parS c₀ n; omega)
  have h1 := one_le_parA n
  have : parS c₀ n - 1 ≤ (parS c₀ n - 1) * parA n := Nat.le_mul_of_pos_right _ h1
  omega

lemma parS_mul_le (c₀ n : ℕ) : parS c₀ n * parA n ≤ n + c₀ + 2 + parA n := by
  obtain ⟨-, hs2⟩ := parS_spec c₀ n
  have := hs2 (parS c₀ n - 1) (by have := one_le_parS c₀ n; omega)
  have e : parS c₀ n * parA n = (parS c₀ n - 1) * parA n + parA n := by
    obtain ⟨k, hk⟩ : ∃ k, parS c₀ n = k + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (one_le_parS c₀ n)).symm⟩
    rw [hk]; simp; ring
  omega

lemma two_le_parS {c₀ : ℕ} (hc : 1 ≤ c₀) (n : ℕ) : 2 ≤ parS c₀ n := by
  obtain ⟨hs1, -⟩ := parS_spec c₀ n
  have ha := parA_le n
  by_contra hlt
  have : parS c₀ n * parA n ≤ 1 * parA n := Nat.mul_le_mul_right _ (by omega)
  omega

lemma packedWidth_par (c₀ n : ℕ) :
    Lax119563.PackedRepresentation.packedWidth n (n + c₀) (parS c₀ n) = parA n := by
  obtain ⟨hs1, -⟩ := parS_spec c₀ n
  have h1 := one_le_parS c₀ n
  unfold Lax119563.PackedRepresentation.packedWidth
  refine max_eq_left ?_
  show _ ≤ parA n
  apply Nat.le_of_lt_succ
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  have : (parA n).succ * parS c₀ n = parS c₀ n * parA n + parS c₀ n := by
    rw [Nat.succ_eq_add_one]; ring
  omega

/-- **The parameter machine.** -/
theorem par_machine (c₀ : ℕ) : ∃ P : Machine, Deterministic P ∧ ∃ K : ℕ, ∀ x : List Bool,
    ComputesWithin P x (encodeNats [x.length + c₀, parS c₀ x.length] ++ x)
      (K * (x.length + c₀ + 4) ^ 3) := by
  refine ⟨(withSuffix ((parProg c₀).machine 10)).compile, withSuffix_deterministic,
    16 * (100 * 64 * 49 + 200), fun x => ?_⟩
  set m := x.length + c₀ + 4 with hm
  have hw2 : 2 ≤ 4 * m := by omega
  have hw : 4 * (x.length + c₀ + 4) < 2 ^ (4 * m) := Nat.lt_two_pow_self
  obtain ⟨hf, he, hc⟩ := good_parProg (x := x) c₀ hw2 hw
  have h := CStm.computesWithin (D := 10) hw2 (parProg_depth c₀) hf
  rw [he] at h
  simp only [st6] at h
  have h2 := withSuffix_computesWithin h
  refine Main.Compose.computesWithin_mono' h2 ?_
  have hlen : (encodeNats [x.length + c₀, parS c₀ x.length]).length ≤
      (2 * (x.length + c₀) + 1) + (2 * parS c₀ x.length + 1) := by
    have e1 := length_encodeNat_le (x.length + c₀)
    have e2 := length_encodeNat_le (parS c₀ x.length)
    simp only [encodeNats, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.length_append]
    omega
  have hsle : parS c₀ x.length ≤ x.length + c₀ + 2 := by
    obtain ⟨-, hs2⟩ := parS_spec c₀ x.length
    have := hs2 (parS c₀ x.length - 1) (by have := one_le_parS c₀ x.length; omega)
    have h1 := one_le_parA x.length
    have : parS c₀ x.length - 1 ≤ (parS c₀ x.length - 1) * parA x.length :=
      Nat.le_mul_of_pos_right _ h1
    omega
  have ht := par_time_arith (cost := cost x (4 * m) (parProg c₀) (NSt.zero 6 0)) hm hsle hc
  have : 16 * (cost x (4 * m) (parProg c₀) (NSt.zero 6 0) +
      20 * (x.length + (encodeNats [x.length + c₀, parS c₀ x.length]).length) + 10 +
      x.length + 1) ≤ 16 * (cost x (4 * m) (parProg c₀) (NSt.zero 6 0) +
      20 * (x.length + ((2 * (x.length + c₀) + 1) + (2 * parS c₀ x.length + 1))) + 10 +
      x.length + 1) := by omega
  omega

end Lax119563Proofs.Hardness

end Hardness_ParMachine

/-! ### Formerly `Lax119563Proofs.Hardness.HorizonMachine` -/

section Hardness_HorizonMachine

/-!
# The machine putting the horizon in front of the input

For constants `s` and `c₀`, the structured program `hzProg s c₀` reads its input `x`, counts
its length `n`, computes `a = ⌈log₂ (n + 2)⌉` (`parA n`) by repeated doubling (as `parProg`),
then `s a` by `s` additions, and emits `[s a + c₀, s]`. Run with word size
`w = a + 2 s + c₀ + 9 = O(log n)`, each word operation costs `O(log² n)`, so the machine
`(withSuffix (hzProg s c₀).machine)` computes `encodeNats [s a + c₀, s] ++ x` from `x`
within `K (n + 1) (a + 1)^2` steps (`horizon_machine`), which is quasi-linear.
-/

open Lax119563.BinaryEncodings Lax119563.DeterministicTime Lax119563Proofs.Reduction
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Hardness

open Compiler Compiler.CStm

/-- The program. -/
def hzProg (s c₀ : ℕ) : CStm 6 0 :=
  .seq (.seq (.rd 0) (.loop (.var 0) (.seq (.set 1 (.add (.var 1) (.const 1))) (.rd 0))))
  (.seq (.seq (.set 2 (.const 1)) (.loop (.lt (.var 2) (.add (.var 1) (.const 2)))
      (.seq (.set 2 (.add (.var 2) (.var 2))) (.set 3 (.add (.var 3) (.const 1))))))
  (.seq (.loop (.lt (.var 5) (.const s))
      (.seq (.set 4 (.add (.var 4) (.var 3))) (.set 5 (.add (.var 5) (.const 1)))))
  (.seq (.emit (.add (.var 4) (.const c₀))) (.emit (.var 5)))))

lemma hzProg_depth (s c₀ : ℕ) : (hzProg s c₀).depth ≤ 10 := by
  simp [hzProg, CStm.depth, Ex.depth]

section Good

variable {x : List Bool} {w : ℕ}

local notation "NC" => Ex.nodeCost w

/-- Phase 3: `s a` by `s` additions. -/
lemma good_hz3 (s n p a : ℕ) (hw : s * a + s < 2 ^ w) :
    Good x w (.loop (.lt (.var 5) (.const s))
      (.seq (.set 4 (.add (.var 4) (.var 3))) (.set 5 (.add (.var 5) (.const 1)))))
      (st6 0 n p a (0 * a) 0 n []) (st6 0 n p a (s * a) s n [])
      ((s + 1) * (20 * NC)) := by
  have hS : ∀ j < s, Good x w
      (.seq (.set 4 (.add (.var 4) (.var 3))) (.set 5 (.add (.var 5) (.const 1))) : CStm 6 0)
      (st6 0 n p a (j * a) j n []) (st6 0 n p a ((j + 1) * a) (j + 1) n []) (8 * NC) := by
    intro j hj
    have hja : j * a + a ≤ s * a := by
      have := Nat.mul_le_mul_right a hj
      rwa [Nat.succ_mul] at this
    have hf1 : (Ex.add (.var 4) (.var 3) : Ex 6).Fits w (st6 0 n p a (j * a) j n []).env := by
      simp [Ex.Fits, st6, Ex.eval]; omega
    have hf2 : (Ex.add (.var 5) (.const 1) : Ex 6).Fits w
        ((st6 0 n p a (j * a) j n []).set 4 (j * a + a)).env := by
      simp [Ex.Fits, st6, Ex.eval, Function.update]
      refine ⟨by omega, ?_, by omega⟩
      rintro rfl
      simp at hw
      omega
    refine ((CStm.Good.set hf1).seq (CStm.Good.set hf2)).of_eq ?_ ?_
    · refine NSt.ext (funext fun i => ?_) rfl rfl rfl
      fin_cases i <;> simp [st6, Ex.eval, Function.update] <;> ring
    · simp only [Ex.size]; have := @unit_le_nc w; omega
  have hl := Good.loop_const (x := x) (w := w)
    (e := (Ex.lt (.var 5) (.const s))) s
    (fun j => st6 0 n p a (j * a) j n []) (8 * NC)
    (fun j hj => by simp [st6, Ex.eval, hj])
    (by simp [st6, Ex.eval])
    (fun j hj => by simp [Ex.Fits, st6]; omega)
    hS
  refine hl.mono ?_
  have := cond_le (w := w) (.lt (.var 5) (.const s)) (by simp [Ex.size])
  have e : (s + 1) * (20 * NC) = s * (20 * NC) + 20 * NC := by ring
  have e2 : s * (8 * NC + condCost w (Ex.lt (.var 5) (.const s) : Ex 6)) ≤
      s * (20 * NC) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- Phase 4: the output. -/
lemma good_hz4 (s c₀ n p a : ℕ) (hw : s * a + c₀ + s < 2 ^ w) :
    Good x w (.seq (.emit (.add (.var 4) (.const c₀))) (.emit (.var 5)) : CStm 6 0)
      (st6 0 n p a (s * a) s n []) (st6 0 n p a (s * a) s n [s * a + c₀, s]) (8 * NC) := by
  refine ((CStm.Good.emit (by simp [Ex.Fits, st6, Ex.eval]; omega)).seq
    (CStm.Good.emit (by simp [Ex.Fits, st6]; omega))).of_eq ?_ ?_
  · simp [st6, Ex.eval]
  · simp only [Ex.size]; have := @unit_le_nc w; omega

/-- **The program.** -/
lemma good_hzProg (s c₀ : ℕ) (hw2 : 2 ≤ w)
    (hw : 4 * (x.length + 4) + s * (x.length + 2) + c₀ + s < 2 ^ w) :
    Good x w (hzProg s c₀) (NSt.zero 6 0)
      (st6 0 x.length (2 ^ parA x.length) (parA x.length) (s * parA x.length) s x.length
        [s * parA x.length + c₀, s])
      (40 * (x.length + s + 4) * NC) := by
  have ha := parA_le x.length
  have hsa : s * parA x.length ≤ s * (x.length + 2) := Nat.mul_le_mul_left _ ha
  have h1 := good_phase1 (x := x) hw2 (by omega)
  have h2 := good_phase2 (x := x) x.length hw2 (by omega)
  have h3 := good_hz3 (x := x) (w := w) s x.length (2 ^ parA x.length) (parA x.length)
    (by omega)
  have h4 := good_hz4 (x := x) (w := w) s c₀ x.length (2 ^ parA x.length) (parA x.length)
    (by omega)
  rw [show (st6 0 x.length (2 ^ parA x.length) (parA x.length) 0 0 x.length [] : NSt 6 0) =
    st6 0 x.length (2 ^ parA x.length) (parA x.length) (0 * parA x.length) 0 x.length [] by
      simp] at h2
  refine (h1.seq (h2.seq (h3.seq h4))).mono ?_
  have e1 : (x.length + 1) * (20 * NC) + ((parA x.length + 1) * (20 * NC) +
      ((s + 1) * (20 * NC) + 8 * NC)) ≤
      (x.length + parA x.length + s + 4) * (20 * NC) := by
    have : 8 * NC ≤ 20 * NC := by omega
    have e : (x.length + parA x.length + s + 4) * (20 * NC) = (x.length + 1) * (20 * NC) +
        ((parA x.length + 1) * (20 * NC) + ((s + 1) * (20 * NC) + 20 * NC)) := by ring
    omega
  have e2 : (x.length + parA x.length + s + 4) * (20 * NC) ≤
      (2 * (x.length + s + 4)) * (20 * NC) := Nat.mul_le_mul_right _ (by omega)
  have e3 : 40 * (x.length + s + 4) * NC = (2 * (x.length + s + 4)) * (20 * NC) := by ring
  omega

end Good

/-! ## The machine -/

/-- The time bound. -/
lemma hz_time_arith {n a s c₀ D cost NC out : ℕ}
    (hcost : cost ≤ 40 * (n + s + 4) * NC) (hNC : NC ≤ 64 * (D + 4) ^ 2 * (a + 1) ^ 2)
    (hout : out ≤ 2 * (s * a + c₀) + 1 + (2 * s + 1)) :
    16 * (cost + 20 * (n + out) + 10 + n + 1) ≤
      16 * (40 * (s + 4) * (64 * (D + 4) ^ 2) + 80 * s + 40 * c₀ + 72) *
        (n + 1) * (a + 1) ^ 2 := by
  obtain ⟨P, hP⟩ : ∃ P, P = (n + 1) * (a + 1) ^ 2 := ⟨_, rfl⟩
  have hA1 : 1 ≤ (a + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hP1 : n + 1 ≤ P := by
    rw [hP]; simpa using Nat.mul_le_mul_left (n + 1) hA1
  have haP : a ≤ P := by
    rw [hP]
    calc a ≤ 1 * (a + 1) ^ 1 := by simp
      _ ≤ (n + 1) * (a + 1) ^ 2 :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
  obtain ⟨A, hA⟩ : ∃ A, A = 64 * (D + 4) ^ 2 := ⟨_, rfl⟩
  rw [← hA] at hNC ⊢
  have h1 : (n + s + 4) * NC ≤ (s + 4) * A * P := by
    calc (n + s + 4) * NC ≤ ((s + 4) * (n + 1)) * (A * (a + 1) ^ 2) :=
          Nat.mul_le_mul (by nlinarith) hNC
      _ = (s + 4) * A * P := by rw [hP]; ring
  have h2 : s * a ≤ s * P := Nat.mul_le_mul_left _ haP
  have h3 : c₀ ≤ c₀ * P := Nat.le_mul_of_pos_right _ (by omega)
  have h4 : 40 * (n + s + 4) * NC = 40 * ((n + s + 4) * NC) := by ring
  have e : 16 * (40 * (s + 4) * A + 80 * s + 40 * c₀ + 72) * (n + 1) * (a + 1) ^ 2 =
      16 * (40 * ((s + 4) * A * P) + 80 * (s * P) + 40 * (c₀ * P) + 72 * P) := by
    rw [hP]; ring
  rw [e]
  have h5 : s ≤ s * P := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- **The horizon machine.** For constants `s` and `c₀` there is a deterministic machine
computing `encodeNats [s ⌈log₂ (n + 2)⌉ + c₀, s] ++ x` from an input `x` of length `n`
within `K (n + 1) (⌈log₂ (n + 2)⌉ + 1)^2` steps. -/
theorem horizon_machine (s c₀ : ℕ) : ∃ P : Machine, Deterministic P ∧ ∃ K : ℕ,
    ∀ x : List Bool,
      ComputesWithin P x (encodeNats [s * parA x.length + c₀, s] ++ x)
        (K * (x.length + 1) * (parA x.length + 1) ^ 2) := by
  obtain ⟨D, hD⟩ : ∃ D, D = 2 * s + c₀ + 9 := ⟨_, rfl⟩
  refine ⟨(withSuffix ((hzProg s c₀).machine 10)).compile, withSuffix_deterministic,
    16 * (40 * (s + 4) * (64 * (D + 4) ^ 2) + 80 * s + 40 * c₀ + 72), fun x => ?_⟩
  obtain ⟨w, hw⟩ : ∃ w, w = parA x.length + D := ⟨_, rfl⟩
  have ha1 := one_le_parA x.length
  have hw2 : 2 ≤ w := by omega
  have hwb : 4 * (x.length + 4) + s * (x.length + 2) + c₀ + s < 2 ^ w := by
    have h1 : 2 ^ w = 2 ^ parA x.length * 2 ^ D := by rw [hw, pow_add]
    have h2 : (x.length + 2) * 2 ^ D ≤ 2 ^ parA x.length * 2 ^ D :=
      Nat.mul_le_mul_right _ (le_pow_parA x.length)
    have h3 : (x.length + 2) * D < (x.length + 2) * 2 ^ D :=
      Nat.mul_lt_mul_of_pos_left Nat.lt_two_pow_self (by omega)
    have h4 : 4 * (x.length + 4) + s * (x.length + 2) + c₀ + s ≤ (x.length + 2) * D := by
      have e : (x.length + 2) * D = (x.length + 2) * (2 * s + c₀ + 9) := by rw [hD]
      have : c₀ + s ≤ (x.length + 2) * (c₀ + s) := Nat.le_mul_of_pos_left _ (by omega)
      rw [e]; nlinarith
    omega
  obtain ⟨hf, he, hc⟩ := good_hzProg (x := x) s c₀ hw2 hwb
  have h := CStm.computesWithin (D := 10) hw2 (hzProg_depth s c₀) hf
  rw [he] at h
  simp only [st6] at h
  have h2 := withSuffix_computesWithin h
  refine Main.Compose.computesWithin_mono' h2 ?_
  have hlen : (encodeNats [s * parA x.length + c₀, s]).length ≤
      2 * (s * parA x.length + c₀) + 1 + (2 * s + 1) := by
    have e1 := length_encodeNat_le (s * parA x.length + c₀)
    have e2 := length_encodeNat_le s
    simp only [encodeNats, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.length_append]
    omega
  have hNC : Ex.nodeCost w ≤ 64 * (D + 1 + 3) ^ 2 * (parA x.length + 1) ^ 2 :=
    nodeCost_le_sq (by rw [hw]; nlinarith)
  exact hz_time_arith hc hNC hlen

end Lax119563Proofs.Hardness

end Hardness_HorizonMachine

/-! ### Formerly `Lax119563Proofs.Hardness.XpProgram` -/

section Hardness_XpProgram

/-!
# Computing the parameters of the XP reduction

For machines `Mκ` (computing a parameter `k` from the input) and `Mf` (computing a function
`F`), the structured statement `xpS Mκ Mf` reads its input `y` with `n = |y|`, computes
`k` and `F k` (`paramS`), then `a = ⌈log₂ (n + 2)⌉` (`parA n`) by doubling and
`h = F k · a` by repeated addition, and emits `[h, F k + 1]`. Its machine computes
`encodeNats [F k · a, F k + 1]` from `y` within `K · g(k)^3 · (n + 1)^(3 (d + 1) + 1)` steps
(`xp_prog`), where `C (n + 1)^d` bounds the running time of `Mκ` and `g` is a computable
function of `k` (`xpG`).

States in the layout of `paramS` with nine extra registers are described by a base state and
the values of the extra registers (`stV`).
-/

open Lax119563.BinaryEncodings Lax119563.DeterministicTime Lax119563Proofs.Reduction
open Lax489179.TuringMachine (Machine Deterministic)
open Lax119563Proofs.Computability Lax119563Proofs.Compiler Lax119563Proofs.Compiler.CStm

namespace Lax119563Proofs.Hardness

variable {C : ℕ}

/-! ## States with nine extra registers -/

/-- The state with base `b` (for the registers below `C` and the stacks) and the values `v`
of the nine extra registers. -/
def stV (b : NSt (C + 9) C) (v : Fin 9 → ℕ) (pos : ℕ) (out : List ℕ) : NSt (C + 9) C :=
  ⟨fun r => if h : C ≤ r.val then v ⟨r.val - C, by omega⟩ else b.env r, b.stk, pos, out⟩

section StV

variable (b : NSt (C + 9) C) (v : Fin 9 → ℕ) (pos : ℕ) (out : List ℕ)

@[simp] lemma stV_ex (i : Fin 9) : (stV b v pos out).env (ex C 9 i) = v i := by
  simp [stV, ex]

lemma stV_set (i : Fin 9) (u : ℕ) :
    (stV b v pos out).set (ex C 9 i) u = stV b (Function.update v i u) pos out := by
  refine NSt.ext (funext fun r => ?_) rfl rfl rfl
  simp only [NSt.set_env, stV]
  by_cases hr : r = ex C 9 i
  · subst hr; simp [ex]
  · rw [Function.update_of_ne hr]
    split_ifs with h
    · have : (⟨r.val - C, by omega⟩ : Fin 9) ≠ i := fun e => hr (by
        ext; simp only [ex, ← e]; omega)
      rw [Function.update_of_ne this]
    · rfl

@[simp] lemma stV_pos' (p : ℕ) : { stV b v pos out with pos := p } = stV b v p out := rfl

@[simp] lemma stV_out' (o : List ℕ) : { stV b v pos out with out := o } = stV b v pos o := rfl

@[simp] lemma stV_pos : (stV b v pos out).pos = pos := rfl
@[simp] lemma stV_outF : (stV b v pos out).out = out := rfl
@[simp] lemma stV_stk : (stV b v pos out).stk = b.stk := rfl

end StV

/-! ## The statement -/

/-- Shorthand for the extra registers. -/
abbrev xr (C : ℕ) (i : Fin 9) : Fin (C + 9) := ex C 9 i

/-- After `paramS`: count the input, compute `a = parA n`, `h = F · a`, and emit `[h, F + 1]`. -/
def tailS (C : ℕ) : CStm (C + 9) C :=
  seqL [.rst, .rd (xr C 3),
    .loop (.var (xr C 3)) (.seq (.set (xr C 4) (.add (.var (xr C 4)) (.const 1))) (.rd (xr C 3))),
    .set (xr C 5) (.const 1),
    .loop (.lt (.var (xr C 5)) (.add (.var (xr C 4)) (.const 2)))
      (.seq (.set (xr C 5) (.add (.var (xr C 5)) (.var (xr C 5))))
        (.set (xr C 6) (.add (.var (xr C 6)) (.const 1)))),
    .loop (.lt (.var (xr C 8)) (.var (xr C 1)))
      (.seq (.set (xr C 7) (.add (.var (xr C 7)) (.var (xr C 6))))
        (.set (xr C 8) (.add (.var (xr C 8)) (.const 1)))),
    .emit (.var (xr C 7)), .emit (.add (.var (xr C 1)) (.const 1))]

/-- The statement of the XP reduction. -/
noncomputable def xpS (Mκ Mf : Machine) : CStm (need Mκ + need Mf + 9) (need Mκ + need Mf) :=
  .seq (paramS Mκ Mf (need Mκ + need Mf) 9 (by omega) (by omega) (by omega))
    (tailS (need Mκ + need Mf))

/-! ## The tail -/

section Tail

variable {x : List Bool} {w : ℕ}

local notation "NC" => Ex.nodeCost w

lemma unit_le_nc' : unitCost w ≤ NC := Ex.unitCost_le_nodeCost w

lemma cond_le' {R : ℕ} (e : Ex R) (hs : e.size ≤ 5) : condCost w e ≤ 6 * NC := by
  unfold condCost
  have : 1 ≤ unitCost w := by unfold unitCost; omega
  have := @unit_le_nc' w
  calc e.size * NC + 1 ≤ 5 * NC + NC := by gcongr; omega
    _ = 6 * NC := by ring

variable (b : NSt (C + 9) C) (k F t : ℕ)

/-- Phase 1: counting the input. -/
lemma tail_phase1 (hw2 : 2 ≤ w) (hw : x.length + 3 < 2 ^ w) :
    Good x w (.loop (.var (xr C 3))
        (.seq (.set (xr C 4) (.add (.var (xr C 4)) (.const 1))) (.rd (xr C 3))) :
        CStm (C + 9) C)
      (stV b ![k, F, t, inBit x 0, 0, 0, 0, 0, 0] (min (0 + 1) x.length) [])
      (stV b ![k, F, t, 0, x.length, 0, 0, 0, 0] x.length [])
      (x.length * (20 * NC) + 6 * NC) := by
  have hS : ∀ j < x.length, Good x w
      (.seq (.set (xr C 4) (.add (.var (xr C 4)) (.const 1))) (.rd (xr C 3)) : CStm (C + 9) C)
      (stV b ![k, F, t, inBit x j, j, 0, 0, 0, 0] (min (j + 1) x.length) [])
      (stV b ![k, F, t, inBit x (j + 1), j + 1, 0, 0, 0, 0] (min (j + 1 + 1) x.length) [])
      (8 * NC) := by
    intro j hj
    have hf : (Ex.add (.var (xr C 4)) (.const 1) : Ex (C + 9)).Fits w
        (stV b ![k, F, t, inBit x j, j, 0, 0, 0, 0] (min (j + 1) x.length) []).env := by
      simp only [Ex.Fits, Ex.eval, xr, stV_ex]
      simp
      omega
    refine ((CStm.Good.set hf).seq (CStm.Good.rd _)).of_eq ?_ ?_
    · rw [stV_set, stV_set]
      simp only [stV_pos', stV_pos, Ex.eval, stV_ex, show min (j + 1) x.length = j + 1 by omega]
      congr 1; funext i; fin_cases i <;> rfl
    · simp only [Ex.size]
      have := @unit_le_nc' w
      omega
  have hl := CStm.Good.loop_const (x := x) (w := w) (e := (.var (xr C 3) : Ex (C + 9))) x.length
    (fun j => stV b ![k, F, t, inBit x j, j, 0, 0, 0, 0] (min (j + 1) x.length) []) (8 * NC)
    (fun j hj => by simpa [Ex.eval] using inBit_lt hj)
    (by simpa [Ex.eval] using inBit_len x)
    (fun j hj => by
      have := inBit_le' x j
      simp [Ex.Fits]; omega)
    hS
  refine hl.of_eq ?_ ?_
  · simp only [inBit_len]
    congr 1; omega
  · have := cond_le' (w := w) (.var (xr C 3)) (by simp [Ex.size])
    have e2 : x.length * (8 * NC + condCost w (.var (xr C 3) : Ex (C + 9))) ≤
        x.length * (20 * NC) := Nat.mul_le_mul_left _ (by omega)
    omega

/-- Phase 2: `a = ⌈log₂ (n + 2)⌉` by doubling. -/
lemma tail_phase2 (hw2 : 2 ≤ w) (n : ℕ) (hw : 4 * (n + 4) < 2 ^ w) :
    Good x w (.loop (.lt (.var (xr C 5)) (.add (.var (xr C 4)) (.const 2)))
      (.seq (.set (xr C 5) (.add (.var (xr C 5)) (.var (xr C 5))))
        (.set (xr C 6) (.add (.var (xr C 6)) (.const 1)))) : CStm (C + 9) C)
      (stV b ![k, F, t, 0, n, 2 ^ 0, 0, 0, 0] n [])
      (stV b ![k, F, t, 0, n, 2 ^ parA n, parA n, 0, 0] n [])
      (parA n * (20 * NC) + 6 * NC) := by
  have hA := pow_parA_le n
  have hS : ∀ j < parA n, Good x w
      (.seq (.set (xr C 5) (.add (.var (xr C 5)) (.var (xr C 5))))
        (.set (xr C 6) (.add (.var (xr C 6)) (.const 1))) : CStm (C + 9) C)
      (stV b ![k, F, t, 0, n, 2 ^ j, j, 0, 0] n [])
      (stV b ![k, F, t, 0, n, 2 ^ (j + 1), j + 1, 0, 0] n []) (8 * NC) := by
    intro j hj
    have hj2 : 2 ^ (j + 1) ≤ 2 ^ parA n := Nat.pow_le_pow_right (by norm_num) hj
    have hja : j + 1 ≤ n + 2 := by have := parA_le n; omega
    rw [pow_succ] at hj2
    have hf1 : (Ex.add (.var (xr C 5)) (.var (xr C 5)) : Ex (C + 9)).Fits w
        (stV b ![k, F, t, 0, n, 2 ^ j, j, 0, 0] n []).env := by
      simp only [Ex.Fits, Ex.eval, xr, stV_ex]; simp; omega
    refine ((CStm.Good.set hf1).seq (CStm.Good.set ?_)).of_eq ?_ ?_
    · rw [stV_set]; simp only [Ex.Fits, Ex.eval, xr, stV_ex]; simp
      omega
    · rw [stV_set, stV_set]
      simp only [Ex.eval, xr, stV_ex]
      rw [show 2 ^ (j + 1) = 2 ^ j + 2 ^ j by ring]
      congr 1; funext i; fin_cases i <;> rfl
    · simp only [Ex.size]; have := @unit_le_nc' w; omega
  have hl := CStm.Good.loop_const (x := x) (w := w)
    (e := (.lt (.var (xr C 5)) (.add (.var (xr C 4)) (.const 2)) : Ex (C + 9))) (parA n)
    (fun j => stV b ![k, F, t, 0, n, 2 ^ j, j, 0, 0] n []) (8 * NC)
    (fun j hj => by simp [Ex.eval, pow_lt_of_lt_parA hj])
    (by simp [Ex.eval, not_lt.mpr (le_pow_parA n)])
    (fun j hj => by
      have : 2 ^ j ≤ 2 ^ parA n := Nat.pow_le_pow_right (by norm_num) hj
      simp only [Ex.Fits, Ex.eval, xr, stV_ex]; simp; omega)
    hS
  refine hl.mono ?_
  have := cond_le' (w := w) (.lt (.var (xr C 5)) (.add (.var (xr C 4)) (.const 2)) : Ex (C + 9))
    (by simp [Ex.size])
  have e2 : parA n * (8 * NC + condCost w
      (.lt (.var (xr C 5)) (.add (.var (xr C 4)) (.const 2)) : Ex (C + 9))) ≤
      parA n * (20 * NC) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- Phase 3: `h = F · a` by repeated addition. -/
lemma tail_phase3 (hw2 : 2 ≤ w) (n a : ℕ) (ha : a ≤ n + 2) (p : ℕ)
    (hw : 4 * ((F + 1) * (n + 4)) < 2 ^ w) :
    Good x w (.loop (.lt (.var (xr C 8)) (.var (xr C 1)))
      (.seq (.set (xr C 7) (.add (.var (xr C 7)) (.var (xr C 6))))
        (.set (xr C 8) (.add (.var (xr C 8)) (.const 1)))) : CStm (C + 9) C)
      (stV b ![k, F, t, 0, n, p, a, 0 * a, 0] n [])
      (stV b ![k, F, t, 0, n, p, a, F * a, F] n [])
      (F * (20 * NC) + 6 * NC) := by
  have hFa : F * a ≤ F * (n + 2) := Nat.mul_le_mul_left _ ha
  have e1 : (F + 1) * (n + 4) = F * (n + 2) + 2 * F + n + 4 := by ring
  have hS : ∀ j < F, Good x w
      (.seq (.set (xr C 7) (.add (.var (xr C 7)) (.var (xr C 6))))
        (.set (xr C 8) (.add (.var (xr C 8)) (.const 1))) : CStm (C + 9) C)
      (stV b ![k, F, t, 0, n, p, a, j * a, j] n [])
      (stV b ![k, F, t, 0, n, p, a, (j + 1) * a, j + 1] n []) (8 * NC) := by
    intro j hj
    have hja : (j + 1) * a ≤ F * a := Nat.mul_le_mul_right _ hj
    have e2 : (j + 1) * a = j * a + a := by ring
    have hf1 : (Ex.add (.var (xr C 7)) (.var (xr C 6)) : Ex (C + 9)).Fits w
        (stV b ![k, F, t, 0, n, p, a, j * a, j] n []).env := by
      simp only [Ex.Fits, Ex.eval, xr, stV_ex]; simp; omega
    refine ((CStm.Good.set hf1).seq (CStm.Good.set ?_)).of_eq ?_ ?_
    · rw [stV_set]; simp only [Ex.Fits, Ex.eval, xr, stV_ex]; simp
      omega
    · rw [stV_set, stV_set]
      simp only [Ex.eval, xr, stV_ex]
      rw [e2]
      congr 1; funext i; fin_cases i <;> rfl
    · simp only [Ex.size]; have := @unit_le_nc' w; omega
  have hl := CStm.Good.loop_const (x := x) (w := w)
    (e := (.lt (.var (xr C 8)) (.var (xr C 1)) : Ex (C + 9))) F
    (fun j => stV b ![k, F, t, 0, n, p, a, j * a, j] n []) (8 * NC)
    (fun j hj => by simp [Ex.eval, hj])
    (by simp [Ex.eval])
    (fun j hj => by simp only [Ex.Fits, xr, stV_ex]; simp; omega)
    hS
  refine hl.mono ?_
  have := cond_le' (w := w) (.lt (.var (xr C 8)) (.var (xr C 1)) : Ex (C + 9))
    (by simp [Ex.size])
  have e2 : F * (8 * NC + condCost w (.lt (.var (xr C 8)) (.var (xr C 1)) : Ex (C + 9))) ≤
      F * (20 * NC) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- **The tail.** -/
lemma tail_good (hw2 : 2 ≤ w) (hw : 4 * ((F + 1) * (x.length + 4)) < 2 ^ w) :
    Good x w (tailS C) (stV b ![k, F, t, 0, 0, 0, 0, 0, 0] x.length [])
      (stV b ![k, F, t, 0, x.length, 2 ^ parA x.length, parA x.length, F * parA x.length, F]
        x.length [F * parA x.length, F + 1])
      (30 * (x.length + parA x.length + F + 1) * NC) := by
  have hn4 : x.length + 4 ≤ (F + 1) * (x.length + 4) := Nat.le_mul_of_pos_left _ (by omega)
  have hFn : F + 1 ≤ (F + 1) * (x.length + 4) := Nat.le_mul_of_pos_right _ (by omega)
  have ha := parA_le x.length
  have hA := pow_parA_le x.length
  have hFa : F * parA x.length ≤ (F + 1) * (x.length + 4) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hU := @unit_le_nc' w
  have g0 := CStm.Good.rst (x := x) (w := w) (st := stV b ![k, F, t, 0, 0, 0, 0, 0, 0] x.length [])
  simp only [stV_pos', stV_pos] at g0
  have g1 : Good x w (.rd (xr C 3) : CStm (C + 9) C) (stV b ![k, F, t, 0, 0, 0, 0, 0, 0] 0 [])
      (stV b ![k, F, t, inBit x 0, 0, 0, 0, 0, 0] (min (0 + 1) x.length) []) (unitCost w) := by
    refine (CStm.Good.rd _).of_eq ?_ le_rfl
    rw [stV_set]; simp only [stV_pos', stV_pos]
    congr 1; funext i; fin_cases i <;> rfl
  have g2 := tail_phase1 (x := x) (w := w) b k F t hw2 (by omega)
  have g3 : Good x w (.set (xr C 5) (.const 1) : CStm (C + 9) C)
      (stV b ![k, F, t, 0, x.length, 0, 0, 0, 0] x.length [])
      (stV b ![k, F, t, 0, x.length, 2 ^ 0, 0, 0, 0] x.length []) (2 * NC) := by
    refine (CStm.Good.set (by simp only [Ex.Fits]; omega)).of_eq ?_ (by simp only [Ex.size]; omega)
    rw [stV_set]; simp only [Ex.eval]
    congr 1; funext i; fin_cases i <;> rfl
  have g4 := tail_phase2 (x := x) (w := w) b k F t hw2 x.length (by omega)
  have g5 := tail_phase3 (x := x) (w := w) b k F t hw2 x.length (parA x.length) ha
    (2 ^ parA x.length) hw
  rw [zero_mul] at g5
  have g6 : Good x w (.emit (.var (xr C 7)) : CStm (C + 9) C)
      (stV b ![k, F, t, 0, x.length, 2 ^ parA x.length, parA x.length, F * parA x.length, F]
        x.length [])
      (stV b ![k, F, t, 0, x.length, 2 ^ parA x.length, parA x.length, F * parA x.length, F]
        x.length [F * parA x.length]) (2 * NC) := by
    refine (CStm.Good.emit ?_).of_eq ?_ (by simp only [Ex.size]; omega)
    · simp only [Ex.Fits, xr, stV_ex]; simp; omega
    · simp only [Ex.eval, xr, stV_ex, stV_out', stV_outF]; simp
  have g7 : Good x w (.emit (.add (.var (xr C 1)) (.const 1)) : CStm (C + 9) C)
      (stV b ![k, F, t, 0, x.length, 2 ^ parA x.length, parA x.length, F * parA x.length, F]
        x.length [F * parA x.length])
      (stV b ![k, F, t, 0, x.length, 2 ^ parA x.length, parA x.length, F * parA x.length, F]
        x.length [F * parA x.length, F + 1]) (4 * NC) := by
    refine (CStm.Good.emit ?_).of_eq ?_ (by simp only [Ex.size]; omega)
    · simp only [Ex.Fits, Ex.eval, xr, stV_ex]; simp; omega
    · simp only [Ex.eval, xr, stV_ex, stV_out', stV_outF]; simp
  refine (g0.seq (g1.seq (g2.seq (g3.seq (g4.seq (g5.seq (g6.seq (g7.seq
    CStm.Good.skip)))))))).mono ?_
  have e : 30 * (x.length + parA x.length + F + 1) * NC =
      30 * (x.length * NC) + 30 * (parA x.length * NC) + 30 * (F * NC) + 30 * NC := by ring
  have e1 : unitCost w * (x.length + 1) ≤ NC * (x.length + 1) := Nat.mul_le_mul_right _ hU
  have e2 : NC * (x.length + 1) = x.length * NC + NC := by ring
  have e3 : x.length * (20 * NC) = 20 * (x.length * NC) := by ring
  have e4 : parA x.length * (20 * NC) = 20 * (parA x.length * NC) := by ring
  have e5 : F * (20 * NC) = 20 * (F * NC) := by ring
  omega

end Tail

/-! ## The whole statement -/

lemma length_encodeNat_le' (m : ℕ) : (encodeNat m).length ≤ 2 * m + 1 := by
  have h1 : (Nat.bits m).length ≤ m := by
    rw [Nat.size_eq_bits_len, Nat.size_le]; exact Nat.lt_two_pow_self
  simp [encodeNat]; omega

/-- The arithmetic of the time bound. -/
lemma xp_arith {Kκ Kf N X P g a sκ kk sf m n L A B : ℕ} (hX : 1 ≤ X) (hP : 1 ≤ P)
    (hg : 1 ≤ g) (hN1 : 1 ≤ N) (hN : N ≤ 64 * g ^ 2 * P ^ 2)
    (h1 : a + sκ + 1 ≤ 3 * g * P * X) (h2 : kk + sf + 1 ≤ 2 * g) (h3 : m ≤ 4 * (g * X))
    (h4 : n + L ≤ 11 * (g * X))
    (hA : A ≤ Kκ * (a + sκ + 1) * N) (hB : B ≤ Kf * (kk + sf + 1) * N) :
    A + B + 9 * N + 30 * m * N + (20 * (n + L) + 10) ≤
      64 * (3 * Kκ + 2 * Kf + 360) * g ^ 3 * (P ^ 3 * X) := by
  have hPX : 1 ≤ P * X := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hgX : 1 ≤ g * X := Nat.one_le_iff_ne_zero.mpr (by positivity)
  set Z := g * P * X * N with hZ
  have eA : A ≤ 3 * Kκ * Z := by
    calc A ≤ Kκ * (a + sκ + 1) * N := hA
      _ ≤ Kκ * (3 * g * P * X) * N := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
      _ = 3 * Kκ * Z := by rw [hZ]; ring
  have eB : B ≤ 2 * Kf * Z := by
    calc B ≤ Kf * (kk + sf + 1) * N := hB
      _ ≤ Kf * (2 * g) * N := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)
      _ ≤ Kf * (2 * g * (P * X)) * N :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hPX))
      _ = 2 * Kf * Z := by rw [hZ]; ring
  have eG : g * X * N ≤ Z := by
    rw [hZ]
    calc g * X * N = g * 1 * X * N := by ring
      _ ≤ g * P * X * N :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hP))
  have eN : N ≤ g * X * N := Nat.le_mul_of_pos_left _ hgX
  have eM : 30 * m * N ≤ 120 * (g * X * N) := by
    calc 30 * m * N ≤ 30 * (4 * (g * X)) * N :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h3)
      _ = 120 * (g * X * N) := by ring
  have eL : g * X ≤ g * X * N := Nat.le_mul_of_pos_right _ hN1
  have hZ' : Z ≤ g * P * X * (64 * g ^ 2 * P ^ 2) := by
    rw [hZ]; exact Nat.mul_le_mul_left _ hN
  have e : (3 * Kκ + 2 * Kf + 360) * Z = 3 * Kκ * Z + 2 * Kf * Z + 360 * Z := by ring
  calc _ ≤ (3 * Kκ + 2 * Kf + 360) * Z := by omega
    _ ≤ (3 * Kκ + 2 * Kf + 360) * (g * P * X * (64 * g ^ 2 * P ^ 2)) :=
        Nat.mul_le_mul_left _ hZ'
    _ = 64 * (3 * Kκ + 2 * Kf + 360) * g ^ 3 * (P ^ 3 * X) := by ring

/-- The computable function of the parameter in the time bound. -/
noncomputable def xpG (Mκ Mf : Machine) (F : ℕ → ℕ) (Cκ k : ℕ) : ℕ :=
  5 + simB Mκ + simB Mf + k + F k + haltTime Mf (encodeNat k) + 2 * Cκ + 16 * (F k + 1)

/-- The constant of the time bound. -/
noncomputable def xpK (Mκ Mf : Machine) : ℕ := 64 * (3 * simK Mκ + 2 * simK Mf + 360)

/-- **The machine of the statement.** If `Mκ` computes `k` from `y` within `Cκ (|y| + 1)^d`
steps, the machine of `xpS Mκ Mf` computes `encodeNats [F k · parA |y|, F k + 1]` from `y`. -/
theorem xp_prog (Mκ Mf : Machine) {F : ℕ → ℕ}
    (hMf : ∀ k, ComputesWithin Mf (encodeNat k) (encodeNat (F k)) (haltTime Mf (encodeNat k)))
    {Cκ d : ℕ} {y : List Bool} {k : ℕ}
    (hκ : ComputesWithin Mκ y (encodeNat k) (Cκ * (y.length + 1) ^ d)) :
    ComputesWithin ((xpS Mκ Mf).machine (xpS Mκ Mf).depth) y
      (encodeNats [F k * parA y.length, F k + 1])
      (xpK Mκ Mf * xpG Mκ Mf F Cκ k ^ 3 * (y.length + 1) ^ (3 * (d + 1) + 1)) := by
  set n := y.length with hn
  set X := n + 1 with hX
  set Pw := X ^ (d + 1) with hPw
  have hPw1 : 1 ≤ Pw := Nat.one_le_pow _ _ (by omega)
  have hXPw : X ≤ Pw := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ Pw := Nat.pow_le_pow_right (by omega) (by omega)
  have hXd : X ^ d ≤ Pw := Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨ht, hht⟩ : ∃ ht, haltTime Mf (encodeNat k) = ht := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, xpG Mκ Mf F Cκ k = g := ⟨_, rfl⟩
  have hgk : g = 5 + simB Mκ + simB Mf + k + F k + ht + 2 * Cκ + 16 * (F k + 1) := by
    rw [← hg, ← hht]; rfl
  rw [hg]
  obtain ⟨w, hwdef⟩ : ∃ w, w = 2 + simB Mκ + simB Mf + k + F k + ht + Cκ + Cκ * Pw +
    4 * ((F k + 1) * (n + 4)) := ⟨_, rfl⟩
  have hw : 2 ≤ w := by omega
  have hsκ : haltTime Mκ y ≤ Cκ * Pw := by
    refine (haltTime_le_of_computesWithin hκ).trans ?_
    exact Nat.mul_le_mul_left _ hXd
  have hlt : ∀ v, v ≤ w → v < 2 ^ w := fun v hv => lt_two_pow_of_le hv
  obtain ⟨st5, g5, e5k, e5v, e5t, e5x, -, -, e5p, e5o⟩ := paramS_good (x := y) (w := w)
    (C := need Mκ + need Mf) (E := 9) (by omega) (by omega) (by omega) hw
    (hlt _ (by omega)).le (hlt _ (by omega)).le (NSt.zero _ _) (bdd_zero _ _ _)
    (by simp [NSt.zero]) (fun q => by simp [NSt.zero]) hκ (hMf k) (hlt _ (by omega))
    (by have := bits_length_le k; omega) (hlt _ (by omega)) (hlt _ (by omega))
    (by have := bits_length_le (F k); omega) (hlt _ (by omega))
  have hv : ∀ i : Fin 9, st5.env (ex _ 9 i) = ![k, F k, ht, 0, 0, 0, 0, 0, 0] i := by
    intro i
    fin_cases i
    · exact e5k
    · exact e5v
    · exact e5t.trans hht
    all_goals (rw [e5x _ (by simp)]; rfl)
  have hst : st5 = stV st5 ![k, F k, ht, 0, 0, 0, 0, 0, 0] n [] := by
    refine NSt.ext (funext fun r => ?_) rfl e5p (by rw [e5o]; rfl)
    simp only [stV]
    split_ifs with h
    · rw [← hv]; congr 1; ext; simp [ex]; omega
    · rfl
  have hW : 4 * ((F k + 1) * (y.length + 4)) ≤ w := by rw [← hn]; omega
  have gt := tail_good (x := y) (w := w) st5 k (F k) ht hw (hlt _ hW)
  rw [← hst] at gt
  have gg : Good y w (xpS Mκ Mf) _ _ _ := g5.seq gt
  have hc := CStm.computesWithin (D := (xpS Mκ Mf).depth) hw le_rfl gg.1
  rw [gg.2.1] at hc
  simp only [stV_outF] at hc
  refine Lax119563Proofs.Reduction.ComputesWithin.mono hc ?_
  have hcost := gg.2.2
  rw [hht] at hcost
  -- the arithmetic
  have hN := Ex.unitCost_le_nodeCost w
  have hN1 : 1 ≤ Ex.nodeCost w := by have := unitCost_ge w; omega
  have hNw : Ex.nodeCost w ≤ 64 * g ^ 2 * Pw ^ 2 := by
    have hw3 : w + 3 ≤ g * Pw := by
      have h0 : (5 + simB Mκ + simB Mf + k + F k + ht + Cκ) ≤
          (5 + simB Mκ + simB Mf + k + F k + ht + Cκ) * Pw := Nat.le_mul_of_pos_right _ hPw1
      have h4 : 4 * ((F k + 1) * (n + 4)) ≤ 16 * (F k + 1) * Pw := by
        have : n + 4 ≤ 4 * Pw := by omega
        calc 4 * ((F k + 1) * (n + 4)) ≤ 4 * ((F k + 1) * (4 * Pw)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ this)
          _ = 16 * (F k + 1) * Pw := by ring
      have h1 : g * Pw = (5 + simB Mκ + simB Mf + k + F k + ht + Cκ) * Pw + Cκ * Pw +
          16 * (F k + 1) * Pw := by rw [hgk]; ring
      omega
    have : Ex.nodeCost w ≤ 64 * (w + 3) ^ 2 := by
      have e : 64 * (w + 3) ^ 2 = (w + 3) * (64 * (w + 3)) := by ring
      rw [e]; simp only [Ex.nodeCost, unitCost]
      exact Nat.mul_le_mul_left _ (by omega)
    calc Ex.nodeCost w ≤ 64 * (w + 3) ^ 2 := this
      _ ≤ 64 * (g * Pw) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw3 2)
      _ = 64 * g ^ 2 * Pw ^ 2 := by ring
  have hg1 : 1 ≤ g := by rw [hgk]; omega
  have h1 : n + haltTime Mκ y + 1 ≤ 3 * g * Pw * X := by
    rw [show 3 * g * Pw * X = 3 * (g * Pw * X) by ring]
    have a1 : X ≤ g * Pw * X := by
      calc X = 1 * 1 * X := by ring
        _ ≤ g * Pw * X := Nat.mul_le_mul_right _ (Nat.mul_le_mul hg1 hPw1)
    have a2 : Cκ * Pw ≤ g * Pw * X := by
      calc Cκ * Pw = Cκ * Pw * 1 := by ring
        _ ≤ g * Pw * X := Nat.mul_le_mul (Nat.mul_le_mul_right _ (by rw [hgk]; omega))
            (by omega)
    omega
  have h2 : (encodeNat k).length + ht + 1 ≤ 2 * g := by
    have := bits_length_le k
    rw [length_encodeNat, hgk]; omega
  have ha := parA_le n
  have hFX : F k + 1 ≤ g * X := by
    calc F k + 1 ≤ g := by rw [hgk]; omega
      _ ≤ g * X := Nat.le_mul_of_pos_right _ (by omega)
  have hnX : n + 1 ≤ g * X := by
    calc n + 1 = 1 * X := by omega
      _ ≤ g * X := Nat.mul_le_mul_right _ hg1
  have h3 : n + parA n + F k + 1 ≤ 4 * (g * X) := by omega
  have h4 : n + (encodeNats [F k * parA n, F k + 1]).length ≤ 11 * (g * X) := by
    have l1 := length_encodeNat_le' (F k * parA n)
    have l2 := length_encodeNat_le' (F k + 1)
    have hFa : F k * parA n ≤ (F k + 1) * (2 * X) := Nat.mul_le_mul (by omega) (by omega)
    have hFa' : (F k + 1) * (2 * X) ≤ 2 * (g * X) := by
      calc (F k + 1) * (2 * X) ≤ g * (2 * X) := Nat.mul_le_mul_right _ (by rw [hgk]; omega)
        _ = 2 * (g * X) := by ring
    simp only [encodeNats, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.length_append]
    omega
  have key := xp_arith (Kκ := simK Mκ) (Kf := simK Mf) (X := X) (P := Pw)
    (a := n) (sκ := haltTime Mκ y) (kk := (encodeNat k).length) (sf := ht)
    (L := (encodeNats [F k * parA n, F k + 1]).length) (by omega) hPw1 hg1 hN1 hNw h1 h2 h3 h4
    (simInCost_le Mκ w _ _) (simNatCost_le Mf w _ _)
  have hpow : Pw ^ 3 * X = X ^ (3 * (d + 1) + 1) := by
    rw [hPw, ← pow_mul, pow_succ, mul_comm (d + 1) 3]
  rw [hpow] at key
  show _ ≤ xpK Mκ Mf * g ^ 3 * X ^ (3 * (d + 1) + 1)
  unfold xpK
  rw [← hn] at hcost ⊢
  omega

end Lax119563Proofs.Hardness

end Hardness_XpProgram

/-! ### Formerly `Lax119563Proofs.Main.TimeReduction` -/

section Main_TimeReduction

/-!
# The quasi-linear reduction from `DTIME(n^s)` to `(s+1)`-WL Distinguishing

The reduction of the time lower bound at fixed dimension (paper, "The time lower bound at
fixed dimension"). For a decider running within `C₀ n^s + C₀` steps, take the horizon
`h = s ⌈log₂ (n + 2)⌉ + c₀` with `2^{c₀} ≥ C₀`, so that `2^h ≥ C₀ n^s + C₀`. The packed
representation with `s` data blocks has block width `ℓ = packedWidth n h s ≤ ⌈log₂(n+2)⌉ + c₀ + 2`,
so `2^ℓ = O(n)` and `h = O(log n)`.

* `pipeline_fine`: the generator of `packed_representation` followed by the machine of
  `matrix_compiler` computes `encodeGraphPair G₀ G₁` from `encodeNats [h, s] ++ x` within
  `C 2^ℓ (h+1)^c` steps with an absolute exponent `c` (the matrix compiler's polylogarithmic
  factor is a power of `log₂ (H + S + 2) = O(h)`).
* `time_reduction`: preceded by the horizon machine (`Hardness.horizon_machine`), this is a
  reduction running in time `C n (log n)^c`, whose output thus has length `≤ C n (log n)^c`.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.BinaryEncodings
  Lax119563.DeterministicTime Lax119563.ImplicitSystemEncodings
  Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.PackedRepresentation
open Lax489179.TuringMachine (Machine Deterministic)
open Lax119563Proofs.Hardness

namespace Lax119563Proofs.Main

/-! ## The pipeline with a quasi-linear time bound -/

lemma packedWidth_le_succ {n h s : ℕ} (hn : n ≤ 2 ^ h) (hh : 1 ≤ h) (hs : 2 ≤ s) :
    packedWidth n h s ≤ h + 1 := by
  unfold packedWidth
  refine max_le ?_ ?_
  · refine Nat.clog_le_of_le_pow ?_
    have : 2 ≤ 2 ^ h := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
    rw [pow_succ]; omega
  · refine Nat.div_le_of_le_mul ?_
    have : 2 * h ≤ s * h := Nat.mul_le_mul_right _ hs
    have e : s * (h + 1) = s * h + s := by ring
    omega

/-- `log₂ N = O(Y)` for `N ≤ A 2^ℓ Y^d` with `ℓ ≤ Y`. -/
lemma log_le_of_le {N A ℓ Y d : ℕ} (hN : N ≤ A * (2 ^ ℓ * Y ^ d)) (hℓ : ℓ ≤ Y) (hY1 : 1 ≤ Y) :
    Nat.log 2 N ≤ (A + d + 1) * Y := by
  rcases Nat.eq_zero_or_pos N with rfl | hN0
  · simp
  have hA : A < 2 ^ A := Nat.lt_two_pow_self
  have hY : Y ^ d ≤ 2 ^ (Y * d) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
  have hlt : N < 2 ^ (A + ℓ + Y * d) := by
    have h1 : A * (2 ^ ℓ * Y ^ d) < 2 ^ A * (2 ^ ℓ * 2 ^ (Y * d)) :=
      Nat.mul_lt_mul_of_lt_of_le hA (Nat.mul_le_mul_left _ hY) (by positivity)
    rw [pow_add, pow_add]
    calc N ≤ A * (2 ^ ℓ * Y ^ d) := hN
      _ < 2 ^ A * (2 ^ ℓ * 2 ^ (Y * d)) := h1
      _ = 2 ^ A * 2 ^ ℓ * 2 ^ (Y * d) := by ring
  have := Nat.log_lt_of_lt_pow (by omega) hlt
  have e : (A + d + 1) * Y = A * Y + Y * d + Y := by ring
  have : A ≤ A * Y := Nat.le_mul_of_pos_right _ hY1
  omega

/-- The time bound of the fine pipeline. -/
lemma fine_time_arith {n s h ℓ T1 H S T2 xin Cs Cc cp cc : ℕ}
    (hs : s ≤ h + 2) (hℓ : ℓ ≤ h + 1) (hn : n ≤ 2 ^ ℓ)
    (hxin : xin ≤ 2 * h + 1 + (2 * s + 1) + n)
    (hT1 : T1 ≤ Cs * s * 2 ^ ℓ * (h + 1) ^ cp) (hH : H ≤ xin + T1)
    (hS : S ≤ 5 * (Cs * (h + 1) ^ 2) * (s + 1) ^ 2 * 2 ^ ℓ * (ℓ + 1))
    (hT2 : T2 ≤ Cc * (H + S) * Nat.log 2 (H + S + 2) ^ cc) :
    2 * T1 + T2 + 3 ≤
      (4 * Cs + Cc * (9 + 92 * Cs) * (9 + 92 * Cs + (cp + 5) + 1) ^ cc + 3) * 2 ^ ℓ *
        (h + 1) ^ (cp + 5 + cc) := by
  obtain ⟨Y, hY⟩ : ∃ Y, Y = h + 1 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 2 ^ ℓ := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = Q * Y ^ (cp + 5) := ⟨_, rfl⟩
  have hY1 : 1 ≤ Y := by omega
  have hQ1 : 1 ≤ Q := hQ ▸ Nat.one_le_two_pow
  have hYk : ∀ k, k ≤ cp + 5 → Q * Y ^ k ≤ P := fun k hk =>
    hP ▸ Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY1 hk)
  rw [← hQ] at hn hT1 hS ⊢
  rw [← hY] at hT1 hS ⊢
  have hs' : s ≤ 2 * Y := by omega
  -- T1
  have hT1' : T1 ≤ 2 * Cs * P := by
    calc T1 ≤ Cs * s * Q * Y ^ cp := hT1
      _ ≤ Cs * (2 * Y) * Q * Y ^ cp :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hs'))
      _ = 2 * Cs * (Q * Y ^ (cp + 1)) := by ring
      _ ≤ 2 * Cs * P := Nat.mul_le_mul_left _ (hYk _ (by omega))
  -- xin
  have hxin' : xin ≤ 7 * P := by
    have h1 : Y ≤ Q * Y ^ 1 := by simpa using Nat.mul_le_mul_right Y hQ1
    have := hYk 1 (by omega)
    have := hYk 0 (by omega)
    simp at this
    omega
  -- S
  have hS' : S ≤ 90 * Cs * P := by
    calc S ≤ 5 * (Cs * Y ^ 2) * (s + 1) ^ 2 * Q * (ℓ + 1) := hS
      _ ≤ 5 * (Cs * Y ^ 2) * (3 * Y) ^ 2 * Q * (2 * Y) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
            (Nat.pow_le_pow_left (by omega) _))) (by omega)
      _ = 90 * Cs * (Q * Y ^ 5) := by ring
      _ ≤ 90 * Cs * P := Nat.mul_le_mul_left _ (hYk _ (by omega))
  have hHS : H + S + 2 ≤ (9 + 92 * Cs) * P := by
    have : 1 ≤ P := le_trans (by simpa using hQ1) (hYk 0 (by omega))
    have e : (9 + 92 * Cs) * P = 9 * P + 92 * Cs * P := by ring
    have e2 : 92 * Cs * P = 2 * Cs * P + 90 * Cs * P := by ring
    omega
  obtain ⟨A, hA⟩ : ∃ A, A = 9 + 92 * Cs := ⟨_, rfl⟩
  rw [← hA] at hHS ⊢
  have hlog : Nat.log 2 (H + S + 2) ≤ (A + (cp + 5) + 1) * Y :=
    log_le_of_le (hHS.trans_eq (by rw [hP, hQ])) (by omega) hY1
  have hT2' : T2 ≤ Cc * A * (A + (cp + 5) + 1) ^ cc * (P * Y ^ cc) := by
    calc T2 ≤ Cc * (H + S) * Nat.log 2 (H + S + 2) ^ cc := hT2
      _ ≤ Cc * (A * P) * ((A + (cp + 5) + 1) * Y) ^ cc :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.pow_le_pow_left hlog _)
      _ = _ := by rw [mul_pow]; ring
  have hPY : P ≤ P * Y ^ cc := Nat.le_mul_of_pos_right _ (by positivity)
  have e : (4 * Cs + Cc * A * (A + (cp + 5) + 1) ^ cc + 3) * Q * Y ^ (cp + 5 + cc) =
      4 * Cs * (P * Y ^ cc) + Cc * A * (A + (cp + 5) + 1) ^ cc * (P * Y ^ cc) +
        3 * (P * Y ^ cc) := by rw [hP]; ring
  rw [e]
  have h1 : 2 * Cs * P ≤ 2 * Cs * (P * Y ^ cc) := Nat.mul_le_mul_left _ hPY
  have h2 : 1 ≤ P := le_trans (by simpa using hQ1) (hYk 0 (by omega))
  have e3 : 4 * Cs * (P * Y ^ cc) = 2 * (2 * Cs * (P * Y ^ cc)) := by ring
  omega

/-- **The pipeline with a quasi-linear time bound**: the packed generator followed by the
matrix compiler, without the leading dimension. -/
theorem pipeline_fine : ∃ c : ℕ, ∀ M : Machine, Deterministic M →
    ∃ R : Machine, Deterministic R ∧ ∃ C : ℕ,
      ∀ (x : List Bool) (h s : ℕ), 2 ≤ x.length → 2 ≤ h → x.length ≤ 2 ^ h → 2 ≤ s →
        s ≤ h + 2 →
        ∃ G₀ G₁ : ColoredGraph,
          ((runOn M x (2 ^ h)).answer.isSome → (Accepts M x ↔ Distinguishes (s + 1) G₀ G₁)) ∧
          ComputesWithin R (encodeNats [h, s] ++ x) (encodeGraphPair G₀ G₁)
            (C * 2 ^ packedWidth x.length h s * (h + 1) ^ c) := by
  obtain ⟨cp, hpack⟩ := packed_representation
  obtain ⟨compile, ⟨Cn, hgame⟩, ⟨Mc, -, Cc, cc, hMc⟩⟩ := matrix_compiler
  refine ⟨cp + 5 + cc, fun M hM => ?_⟩
  obtain ⟨sys, Cs, hsys, Rp, -, hRp⟩ := hpack M hM
  refine ⟨(Compose.comp Rp Mc false fun _ => false).toMachine,
    AMachine.toMachine_deterministic _,
    4 * Cs + Cc * (9 + 92 * Cs) * (9 + 92 * Cs + (cp + 5) + 1) ^ cc + 3,
    fun x h s hx hh hxh hs hsh => ?_⟩
  have hℓ1 := one_le_packedWidth x.length h s
  have hQ := length_add_two_le x.length h s
  obtain ⟨hcorr, hloc, hsch⟩ := hsys x h s hx hh hxh hs hsh
  obtain ⟨Ck, hCk⟩ := hgame (s + 1) (by omega)
  obtain ⟨hsp, hdu, -, -⟩ := hCk _ hℓ1 (sys x h s)
  have hSz : matrixSize (sys x h s) ≤ 5 * (Cs * (h + 1) ^ 2) * (s + 1) ^ 2 *
      2 ^ packedWidth x.length h s * (packedWidth x.length h s + 1) :=
    (sizeParameter_le _).trans (size_arith hloc hsch)
  refine ⟨(compile (sys x h s)).1, (compile (sys x h s)).2, fun hhalt => ?_, ?_⟩
  · exact (hcorr hhalt).symm.trans
      (Hardness.distinguishes_iff_conflict (by omega) _ hsp hdu).symm
  · have h1 := hRp x h s hx hh hxh hs hsh
    have h2 := hMc (s + 1) (by omega) _ hℓ1 (sys x h s)
    have hxin2 : 2 ≤ (encodeNats [h, s] ++ x).length := by simp; omega
    have hc := Compose.compose_computesWithin Rp Mc false (fun _ => false) hxin2 h1 h2
    refine Compose.computesWithin_mono' hc ?_
    have hxin : (encodeNats [h, s] ++ x).length ≤ 2 * h + 1 + (2 * s + 1) + x.length := by
      have e1 := length_encodeNat_le h
      have e2 := length_encodeNat_le s
      simp only [encodeNats, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.length_append]
      omega
    have hH := length_le_of_computesWithin h1
    exact fine_time_arith hsh (packedWidth_le_succ hxh (by omega) hs) (by omega)
      hxin le_rfl hH hSz le_rfl

/-! ## The reduction -/

lemma parA_le_log {n : ℕ} (hn : 2 ≤ n) : parA n ≤ Nat.log 2 n + 2 := by
  unfold parA
  refine Nat.clog_le_of_le_pow ?_
  have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
  rw [pow_succ] at h1 ⊢
  rw [pow_succ]
  have : 1 ≤ 2 ^ Nat.log 2 n := Nat.one_le_two_pow
  omega

lemma one_le_log {n : ℕ} (hn : 2 ≤ n) : 1 ≤ Nat.log 2 n :=
  Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)

lemma packedWidth_le_horizon (n s a c₀ : ℕ) (hs : 1 ≤ s) (ha : Nat.clog 2 (n + 2) = a) :
    packedWidth n (s * a + c₀) s ≤ a + c₀ + 2 := by
  unfold packedWidth
  refine max_le (by omega) (Nat.div_le_of_le_mul ?_)
  have : c₀ ≤ s * c₀ := Nat.le_mul_of_pos_left _ hs
  have e : s * (a + c₀ + 2) = s * a + s * c₀ + 2 * s := by ring
  omega

/-- The halting bound: `C₀ n^s + C₀ ≤ 2^{s a + c₀}` for `n + 2 ≤ 2^a` and `C₀ < 2^{c₀}`. -/
lemma halt_le {C₀ n s a c₀ : ℕ} (hs : 1 ≤ s) (ha : n + 2 ≤ 2 ^ a) (hc : C₀ ≤ 2 ^ c₀) :
    C₀ * n ^ s + C₀ ≤ 2 ^ (s * a + c₀) := by
  have h1 : n ^ s < (n + 2) ^ s := Nat.pow_lt_pow_left (by omega) (by omega)
  have h2 : (n + 2) ^ s ≤ (2 ^ a) ^ s := Nat.pow_le_pow_left ha _
  have e : 2 ^ (s * a + c₀) = (2 ^ a) ^ s * 2 ^ c₀ := by rw [pow_add, ← pow_mul, mul_comm a s]
  rw [e]
  calc C₀ * n ^ s + C₀ = C₀ * (n ^ s + 1) := by ring
    _ ≤ 2 ^ c₀ * (2 ^ a) ^ s := Nat.mul_le_mul hc (by omega)
    _ = _ := by ring

/-- The time bound of the reduction. -/
lemma red_arith {n Lg a TP TR KP Cf E B cf : ℕ} (hn : 1 ≤ n) (hLg : 1 ≤ Lg)
    (ha : a + 1 ≤ 4 * Lg) (hTP : TP ≤ KP * (n + 1) * (a + 1) ^ 2)
    (hTR : TR ≤ Cf * (E * n) * (B * Lg) ^ cf) :
    n + (2 * TP + TR + 3) ≤ (64 * KP + Cf * E * B ^ cf + 4) * n * Lg ^ (cf + 2) := by
  obtain ⟨W, hW⟩ : ∃ W, W = n * Lg ^ (cf + 2) := ⟨_, rfl⟩
  have hL2 : Lg ^ 2 ≤ Lg ^ (cf + 2) := Nat.pow_le_pow_right hLg (by omega)
  have hLc : Lg ^ cf ≤ Lg ^ (cf + 2) := Nat.pow_le_pow_right hLg (by omega)
  have hnW : n ≤ W := hW ▸ Nat.le_mul_of_pos_right _ (by positivity)
  have hTP' : TP ≤ 32 * KP * W := by
    calc TP ≤ KP * (2 * n) * (4 * Lg) ^ 2 :=
          hTP.trans (Nat.mul_le_mul (Nat.mul_le_mul_left KP (show n + 1 ≤ 2 * n by omega))
            (Nat.pow_le_pow_left ha 2))
      _ = 32 * KP * (n * Lg ^ 2) := by ring
      _ ≤ 32 * KP * W := Nat.mul_le_mul_left _ (hW ▸ Nat.mul_le_mul_left _ hL2)
  have hTR' : TR ≤ Cf * E * B ^ cf * W := by
    calc TR ≤ Cf * (E * n) * (B * Lg) ^ cf := hTR
      _ = Cf * E * B ^ cf * (n * Lg ^ cf) := by rw [mul_pow]; ring
      _ ≤ Cf * E * B ^ cf * W := Nat.mul_le_mul_left _ (hW ▸ Nat.mul_le_mul_left _ hLc)
  have e : (64 * KP + Cf * E * B ^ cf + 4) * n * Lg ^ (cf + 2) =
      2 * (32 * KP * W) + Cf * E * B ^ cf * W + 4 * W := by rw [hW]; ring
  omega

/-- **The quasi-linear reduction from `DTIME(n^s)` to `(s+1)`-WL Distinguishing** (with an
absolute exponent `c`). The output length is bounded by the running time. -/
theorem time_reduction : ∃ c : ℕ, ∀ s : ℕ, 2 ≤ s → ∀ M : Machine, Deterministic M →
    (∃ C₀ : ℕ, ∀ x : List Bool, (runOn M x (C₀ * x.length ^ s + C₀)).answer.isSome) →
    ∃ R : Machine, Deterministic R ∧ ∃ C : ℕ, ∀ x : List Bool, 2 ≤ x.length →
      ∃ G₀ G₁ : ColoredGraph,
        (Accepts M x ↔ Distinguishes (s + 1) G₀ G₁) ∧
        (encodeGraphPair G₀ G₁).length ≤ C * x.length * Nat.log 2 x.length ^ c ∧
        ComputesWithin R x (encodeGraphPair G₀ G₁) (C * x.length * Nat.log 2 x.length ^ c) := by
  obtain ⟨cf, hfine⟩ := pipeline_fine
  refine ⟨cf + 2, fun s hs M hM ⟨C₀, hC₀⟩ => ?_⟩
  obtain ⟨Rf, -, Cf, hRf⟩ := hfine M hM
  obtain ⟨Pm, -, KP, hP⟩ := horizon_machine s (C₀ + 2)
  refine ⟨(Compose.comp Pm Rf false fun _ => false).toMachine,
    AMachine.toMachine_deterministic _,
    64 * KP + Cf * 2 ^ (C₀ + 2 + 4) * (3 * s + (C₀ + 2) + 1) ^ cf + 4, fun x hx => ?_⟩
  obtain ⟨a, ha⟩ : ∃ a, a = parA x.length := ⟨_, rfl⟩
  have ha1 : 1 ≤ a := ha ▸ one_le_parA _
  have hapow : x.length + 2 ≤ 2 ^ a := ha ▸ le_pow_parA _
  have hapow' : 2 ^ a ≤ 2 * (x.length + 2) := ha ▸ pow_parA_le _
  have hsa : s ≤ s * a := Nat.le_mul_of_pos_right _ ha1
  have hxh : x.length ≤ 2 ^ (s * a + (C₀ + 2)) :=
    le_trans (by omega) (Nat.pow_le_pow_right (by norm_num) (show a ≤ s * a + (C₀ + 2) by
      have : a ≤ s * a := Nat.le_mul_of_pos_left _ (by omega)
      omega))
  obtain ⟨G₀, G₁, hacc, hcomp⟩ := hRf x (s * a + (C₀ + 2)) s hx (by omega) hxh hs (by omega)
  -- the machine halts within `2^h` steps
  have hhalt : (runOn M x (2 ^ (s * a + (C₀ + 2)))).answer.isSome := by
    have hle := halt_le (C₀ := C₀) (n := x.length) (s := s) (c₀ := C₀ + 2) (by omega) hapow
      (le_trans Nat.lt_two_pow_self.le (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [runOn_eq_of_le M x hle (hC₀ x)]
    exact hC₀ x
  -- the reduction
  have hPx := hP x
  rw [← ha] at hPx
  have hred := Compose.compose_computesWithin Pm Rf false (fun _ => false) hx hPx hcomp
  obtain ⟨Lg, hLg⟩ : ∃ Lg, Lg = Nat.log 2 x.length := ⟨_, rfl⟩
  have hLg1 : 1 ≤ Lg := hLg ▸ one_le_log hx
  have haL : a ≤ Lg + 2 := ha ▸ hLg ▸ parA_le_log hx
  have hℓ : packedWidth x.length (s * a + (C₀ + 2)) s ≤ a + (C₀ + 2) + 2 :=
    packedWidth_le_horizon _ _ _ _ (by omega) ha.symm
  have hQ : 2 ^ packedWidth x.length (s * a + (C₀ + 2)) s ≤ 2 ^ (C₀ + 2 + 4) * x.length := by
    calc 2 ^ packedWidth x.length (s * a + (C₀ + 2)) s ≤ 2 ^ (a + (C₀ + 2) + 2) :=
          Nat.pow_le_pow_right (by norm_num) hℓ
      _ = 2 ^ a * 2 ^ (C₀ + 2 + 2) := by rw [← pow_add]; ring_nf
      _ ≤ (4 * x.length) * 2 ^ (C₀ + 2 + 2) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ (C₀ + 2 + 4) * x.length := by rw [pow_add 2 (C₀ + 2) 4, pow_add 2 (C₀ + 2) 2]; ring
  have hY : s * a + (C₀ + 2) + 1 ≤ (3 * s + (C₀ + 2) + 1) * Lg := by
    have : s * a ≤ s * (3 * Lg) := Nat.mul_le_mul_left _ (by omega)
    have e : (3 * s + (C₀ + 2) + 1) * Lg = s * (3 * Lg) + (C₀ + 2 + 1) * Lg := by ring
    have : (C₀ + 2 + 1) * 1 ≤ (C₀ + 2 + 1) * Lg := Nat.mul_le_mul_left _ hLg1
    omega
  have hTR : Cf * 2 ^ packedWidth x.length (s * a + (C₀ + 2)) s * (s * a + (C₀ + 2) + 1) ^ cf ≤
      Cf * (2 ^ (C₀ + 2 + 4) * x.length) * ((3 * s + (C₀ + 2) + 1) * Lg) ^ cf :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hQ) (Nat.pow_le_pow_left hY _)
  have hT := red_arith (n := x.length) (a := a) (Lg := Lg) (KP := KP) (by omega) hLg1 (by omega)
    le_rfl hTR
  rw [← hLg]
  have hlen := length_le_of_computesWithin hred
  refine ⟨G₀, G₁, ?_, ?_, Compose.computesWithin_mono' hred ?_⟩
  · rw [hacc hhalt]
  · omega
  · omega

end Lax119563Proofs.Main

end Main_TimeReduction

/-! ### Formerly `Lax119563Proofs.Reduction.PkParse` -/

section Reduction_PkParse

/-!
# The preprocessor of the packed generator

A structured statement `pkPre` (`Compiler.CStm`, number registers, no stacks) reads `h, s`
from the input `encodeNats [h, s] ++ x`, computes `2^q`, `q = ⌈(h + 2)/s⌉`, by a loop, and
emits the records `pkRec x h s k` for `k < pkLen |x| h s` (reading the bits of `x` with `rd`).
**`pkPre_computesWithin`**: its machine computes `pkInput x h s` within
`C (2^ℓ + h + 2) (h + 1)^2` steps.
-/

namespace Lax119563Proofs.Reduction

open Lax119563.BinaryEncodings Lax119563.DeterministicTime Lax119563Proofs.Compiler
open Lax119563Proofs.Compiler.CStm (rdNumS rdNumFinal rdNumS_good)

namespace PkParse

/-- Registers: `0 h, 1 s, 2 acc, 3 P, 4 k, 5 b, 6, 7` (helpers of `rdNumS`). -/
abbrev rH : Fin 8 := 0
abbrev rS : Fin 8 := 1
abbrev rA : Fin 8 := 2
abbrev rP : Fin 8 := 3
abbrev rK : Fin 8 := 4
abbrev rB : Fin 8 := 5
abbrev rU : Fin 8 := 6
abbrev rT : Fin 8 := 7

/-- `2 a`. -/
def dbl (a : Ex 8) : Ex 8 := .add a a

/-- The condition of the first loop: `acc < h + 2 + s`. -/
def c1 : Ex 8 := .lt (.var rA) (.add (.add (.var rH) (.const 2)) (.var rS))

/-- The body of the first loop: `acc += s; P += P`. -/
def b1 : CStm 8 0 := .seq (.set rA (.add (.var rA) (.var rS))) (.set rP (.add (.var rP) (.var rP)))

/-- The condition of the second loop: `b ≠ 0 ∨ k < h ∨ k < s ∨ k < P`. -/
def c2 : Ex 8 := .add (.add (.lt (.const 0) (.var rB)) (.lt (.var rK) (.var rH)))
  (.add (.lt (.var rK) (.var rS)) (.lt (.var rK) (.var rP)))

/-- The first number of a record. -/
def e1 : Ex 8 := .add (.add (.const 8) (.half (.var rB)))
  (.add (dbl (.lt (.const 0) (.var rB))) (dbl (dbl (.lt (.var rK) (.var rH)))))

/-- The second number of a record. -/
def e2 : Ex 8 := .add (.const 4) (.lt (.var rK) (.var rS))

/-- The body of the second loop. -/
def b2 : CStm 8 0 := .seq (.emit e1) (.seq (.emit e2) (.seq (.set rK (.add (.var rK) (.const 1)))
  (.rd rB)))

/-- **The preprocessor.** -/
def pkPre : CStm 8 0 :=
  .seq (rdNumS rH rU rT) (.seq (rdNumS rS rU rT) (.seq (.set rA (.add (.var rS) (.var rS)))
    (.seq (.set rP (.const 2)) (.seq (.loop c1 b1) (.seq (.set rK (.const 0))
      (.seq (.rd rB) (.loop c2 b2)))))))

/-- Environments. -/
def envP (a0 a1 a2 a3 a4 a5 a6 a7 : ℕ) : Fin 8 → ℕ := ![a0, a1, a2, a3, a4, a5, a6, a7]


section Get
variable (a0 a1 a2 a3 a4 a5 a6 a7 : ℕ)
@[simp] lemma envP_H : envP a0 a1 a2 a3 a4 a5 a6 a7 rH = a0 := rfl
@[simp] lemma envP_S : envP a0 a1 a2 a3 a4 a5 a6 a7 rS = a1 := rfl
@[simp] lemma envP_A : envP a0 a1 a2 a3 a4 a5 a6 a7 rA = a2 := rfl
@[simp] lemma envP_P : envP a0 a1 a2 a3 a4 a5 a6 a7 rP = a3 := rfl
@[simp] lemma envP_K : envP a0 a1 a2 a3 a4 a5 a6 a7 rK = a4 := rfl
@[simp] lemma envP_B : envP a0 a1 a2 a3 a4 a5 a6 a7 rB = a5 := rfl
end Get

lemma upd_envP (a0 a1 a2 a3 a4 a5 a6 a7 v : ℕ) :
    Function.update (envP a0 a1 a2 a3 a4 a5 a6 a7) rA v = envP a0 a1 v a3 a4 a5 a6 a7 ∧
    Function.update (envP a0 a1 a2 a3 a4 a5 a6 a7) rP v = envP a0 a1 a2 v a4 a5 a6 a7 ∧
    Function.update (envP a0 a1 a2 a3 a4 a5 a6 a7) rK v = envP a0 a1 a2 a3 v a5 a6 a7 ∧
    Function.update (envP a0 a1 a2 a3 a4 a5 a6 a7) rB v = envP a0 a1 a2 a3 a4 v a6 a7 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i <;> fin_cases i <;> rfl

section Sem

variable (x : List Bool) (h s : ℕ)

/-- The input. -/
abbrev inp : List Bool := encodeNats [h, s] ++ x

/-- The position after the two numbers. -/
abbrev p0 : ℕ := (encodeNat h).length + (encodeNat s).length

/-- The helper value after reading `s`. -/
abbrev uS : ℕ := 2 ^ (Nat.bits s).length

/-- The number of iterations of the first loop. -/
abbrev n1 : ℕ := (h + 1 + s) / s - 1

/-- The state after reading `h, s`. -/
def stR : NSt 8 0 := ⟨envP h s 0 0 0 0 (uS s) 1, fun _ => [], p0 h s, []⟩

/-- The states of the first loop. -/
def S1 (j : ℕ) : NSt 8 0 :=
  ⟨envP h s ((j + 2) * s) (2 ^ (j + 1)) 0 0 (uS s) 1, fun _ => [], p0 h s, []⟩

/-- The states of the second loop. -/
def S2 (j : ℕ) : NSt 8 0 :=
  ⟨envP h s ((n1 h s + 2) * s) (2 ^ ((h + 1 + s) / s)) j (inBit (inp x h s) (p0 h s + j)) (uS s) 1,
    fun _ => [], min (p0 h s + j + 1) (inp x h s).length,
    (List.range j).flatMap (pkRec x h s)⟩

end Sem

lemma drop_inp (x : List Bool) (h s j : ℕ) : (inp x h s).drop (p0 h s + j) = x.drop j := by
  rw [Compiler.drop_add]
  have : (inp x h s).drop (p0 h s) = x := by
    rw [show p0 h s = (encodeNats [h, s]).length by simp [encodeNats]]
    exact List.drop_left
  rw [this]

lemma inBit_inp (x : List Bool) (h s j : ℕ) : inBit (inp x h s) (p0 h s + j) = inBit x j := by
  unfold inBit; rw [drop_inp]

lemma inBit_min (l : List Bool) (p : ℕ) : inBit l (min p l.length) = inBit l p := by
  rcases le_total p l.length with hp | hp
  · rw [min_eq_left hp]
  · rw [min_eq_right hp]
    unfold inBit
    rw [List.drop_eq_nil_of_le le_rfl, List.drop_eq_nil_of_le hp]

lemma inBit_pos (x : List Bool) (j : ℕ) : 0 < inBit x j ↔ j < x.length := by
  unfold inBit
  rcases Nat.lt_or_ge j x.length with hj | hj
  · rw [List.drop_eq_getElem_cons hj]; simp [rdVal, hj]
  · rw [List.drop_eq_nil_of_le hj]; simp [rdVal]; omega

lemma inBit_x_cases (x : List Bool) (j : ℕ) :
    inBit x j / 2 = (x.getD j false).toNat ∧ (if 0 < inBit x j then 1 else 0) =
      (if j < x.length then 1 else 0) := by
  unfold inBit
  rcases Nat.lt_or_ge j x.length with hj | hj
  · rw [List.drop_eq_getElem_cons hj, List.getD_eq_getElem _ _ hj]
    cases x[j] <;> simp [rdVal, hj]
  · rw [List.drop_eq_nil_of_le hj, List.getD_eq_default _ _ hj]
    simp [rdVal, show ¬ j < x.length by omega]


open CStm in
lemma stR_eq (h s : ℕ) :
    rdNumFinal (rdNumFinal (NSt.zero 8 0) rH rU rT h) rS rU rT s = stR h s := by
  simp only [rdNumFinal, stR, NSt.zero]
  congr 1
  · funext i; fin_cases i <;> simp [Function.update, envP, rT, rU, rS, rH]
  · simp

lemma c1_iff {h s j : ℕ} (hs : 1 ≤ s) : (j + 2) * s < h + 2 + s ↔ j < n1 h s := by
  have hq : 1 ≤ (h + 1 + s) / s := (Nat.le_div_iff_mul_le hs).mpr (by omega)
  have : (j + 2) * s < h + 2 + s ↔ j + 2 ≤ (h + 1 + s) / s := by
    rw [Nat.le_div_iff_mul_le hs]; omega
  rw [this]; unfold n1; omega

lemma acc_le {h s j : ℕ} (hs : 1 ≤ s) (hj : j ≤ n1 h s) : (j + 2) * s ≤ h + 1 + 2 * s := by
  have h1 : (h + 1 + s) / s * s ≤ h + 1 + s := Nat.div_mul_le_self _ _
  have hq : 1 ≤ (h + 1 + s) / s := (Nat.le_div_iff_mul_le hs).mpr (by omega)
  have h2 : (j + 2) * s ≤ ((h + 1 + s) / s + 1) * s := Nat.mul_le_mul_right _ (by unfold n1 at hj; omega)
  have e : ((h + 1 + s) / s + 1) * s = (h + 1 + s) / s * s + s := by ring
  omega

lemma q_le {h s : ℕ} (hh : 1 ≤ h) (hs : 2 ≤ s) : (h + 1 + s) / s ≤ h + 1 := by
  apply Nat.div_le_of_le_mul; nlinarith

open CStm Good in
/-- **The preprocessor**: denotation and cost. -/
theorem pkPre_good {x : List Bool} {h s : ℕ} (hx : 2 ≤ x.length) (hh : 2 ≤ h)
    (hxh : x.length ≤ 2 ^ h) (hs : 2 ≤ s) (hsh : s ≤ h + 2) :
    CStm.Good (inp x h s) (h + 6) pkPre (NSt.zero 8 0) (S2 x h s (pkLen x.length h s))
      (1000 * Ex.nodeCost (h + 6) * ((encodeNat h).length + (encodeNat s).length +
        n1 h s + pkLen x.length h s + 10)) := by
  have hw2 : 2 ≤ h + 6 := by omega
  have hs1 : 1 ≤ s := by omega
  have hpw : 2 ^ (h + 6) = 64 * 2 ^ h := by rw [pow_add]; ring
  have hhb : h < 2 ^ h := Nat.lt_two_pow_self
  have hq := q_le (h := h) (by omega) hs
  have hP : 2 ^ ((h + 1 + s) / s) ≤ 2 * 2 ^ h := by
    calc 2 ^ ((h + 1 + s) / s) ≤ 2 ^ (h + 1) := Nat.pow_le_pow_right (by norm_num) hq
      _ = 2 * 2 ^ h := by rw [pow_succ]; ring
  have hm : pkLen x.length h s ≤ 4 * 2 ^ h := by
    unfold pkLen; omega
  have hbits : ∀ v, v ≤ h + 2 → (Nat.bits v).length < h + 6 := fun v hv => by
    rw [Nat.size_eq_bits_len]
    have : v < 2 ^ (h + 5) := by
      have : 2 ^ (h + 5) = 32 * 2 ^ h := by rw [pow_add]; ring
      omega
    have := Nat.size_le.mpr this
    omega
  -- reading `h` and `s`
  have g1 := rdNumS_good (x := inp x h s) hw2 (r := rH) (p := rU) (t := rT) (by decide) (by decide)
    (by decide) (NSt.zero 8 0) h (encodeNat s ++ x) (by simp [NSt.zero, inp, encodeNats])
    (hbits h (by omega))
  have g2 := rdNumS_good (x := inp x h s) hw2 (r := rS) (p := rU) (t := rT) (by decide) (by decide)
    (by decide) (rdNumFinal (NSt.zero 8 0) rH rU rT h) s x
    (by
      simp only [rdNumFinal, NSt.zero, zero_add]
      rw [show inp x h s = encodeNat h ++ (encodeNat s ++ x) by simp [inp, encodeNats]]
      exact List.drop_left)
    (hbits s (by omega))
  rw [stR_eq] at g2
  -- initializing the first loop
  have g3 : CStm.Good (inp x h s) (h + 6) (.set rA (.add (.var rS) (.var rS))) (stR h s)
      ((stR h s).set rA (s + s)) (3 * Ex.nodeCost (h + 6) + unitCost (h + 6)) := by
    refine (CStm.Good.set ?_).of_eq rfl (by simp [Ex.size])
    simp only [Ex.Fits, Ex.eval, stR, envP_S]
    omega
  have g4 : CStm.Good (inp x h s) (h + 6) (.set rP (.const 2)) ((stR h s).set rA (s + s))
      (S1 h s 0) (Ex.nodeCost (h + 6) + unitCost (h + 6)) := by
    refine (CStm.Good.set ?_).of_eq ?_ (by simp [Ex.size])
    · simp only [Ex.Fits]; omega
    · simp only [stR, S1, NSt.set, Ex.eval, NSt.set_env]
      rw [(upd_envP _ _ _ _ _ _ _ _ _).1, (upd_envP _ _ _ _ _ _ _ _ _).2.1]
      congr 2; ring
  -- the first loop
  have hq1 : 1 ≤ (h + 1 + s) / s := (Nat.le_div_iff_mul_le hs1).mpr (by omega)
  have g5 : CStm.Good (inp x h s) (h + 6) (.loop c1 b1) (S1 h s 0) (S1 h s (n1 h s))
      (n1 h s * (2 * (3 * Ex.nodeCost (h + 6) + unitCost (h + 6)) + condCost (h + 6) c1) +
        condCost (h + 6) c1) := by
    refine CStm.Good.loop_const (n1 h s) (S1 h s) _ (fun j hj => ?_) ?_ (fun j hj => ?_)
      (fun j hj => ?_)
    · have hc := (c1_iff (h := h) hs1).mpr hj
      simp only [c1, S1, Ex.eval, envP_A, envP_H, envP_S]
      simp [hc]
    · have hc : ¬ (n1 h s + 2) * s < h + 2 + s := fun h' =>
        lt_irrefl _ ((c1_iff hs1).mp h')
      simp only [c1, S1, Ex.eval, envP_A, envP_H, envP_S]
      simp [hc]
    · have ha := acc_le (h := h) hs1 hj
      simp only [c1, S1, Ex.Fits, Ex.eval, envP_A, envP_H, envP_S]
      omega
    · have ha := acc_le (h := h) hs1 (show j + 1 ≤ n1 h s by omega)
      have ha0 := acc_le (h := h) hs1 (show j ≤ n1 h s by omega)
      have hp : 2 ^ (j + 1) + 2 ^ (j + 1) ≤ 2 * 2 ^ h := by
        have : 2 ^ (j + 2) ≤ 2 ^ ((h + 1 + s) / s) :=
          Nat.pow_le_pow_right (by norm_num) (by unfold n1 at hj; omega)
        rw [pow_succ 2 (j + 1)] at this; omega
      refine (CStm.Good.seq (CStm.Good.set ?_) (CStm.Good.set ?_)).of_eq ?_
        (by simp [Ex.size]; omega)
      · simp only [Ex.Fits, S1, envP_A, envP_S, Ex.eval]
        refine ⟨by omega, by omega, ?_⟩
        have : (j + 2) * s + s = (j + 1 + 2) * s := by ring
        omega
      · simp only [Ex.Fits, S1, NSt.set, Ex.eval]
        rw [(upd_envP _ _ _ _ _ _ _ _ _).1]
        simp only [envP_P]
        omega
      · simp only [S1, NSt.set, Ex.eval]
        rw [(upd_envP _ _ _ _ _ _ _ _ _).1]
        simp only [envP_A, envP_S, envP_P]
        rw [(upd_envP _ _ _ _ _ _ _ _ _).2.1]
        congr 2
        · ring
        · rw [pow_succ 2 (j + 1)]; ring
  -- the second loop
  have g6 : CStm.Good (inp x h s) (h + 6) (.set rK (.const 0)) (S1 h s (n1 h s))
      (S1 h s (n1 h s)) (Ex.nodeCost (h + 6) + unitCost (h + 6)) := by
    refine (CStm.Good.set ?_).of_eq ?_ (by simp [Ex.size])
    · simp only [Ex.Fits]; omega
    · simp only [S1, NSt.set, Ex.eval]
      rw [(upd_envP _ _ _ _ _ _ _ _ _).2.2.1]
  have g7 : CStm.Good (inp x h s) (h + 6) (.rd rB) (S1 h s (n1 h s)) (S2 x h s 0)
      (unitCost (h + 6)) := by
    refine (CStm.Good.rd rB).of_eq ?_ le_rfl
    simp only [S1, S2, NSt.set]
    rw [(upd_envP _ _ _ _ _ _ _ _ _).2.2.2]
    have : n1 h s + 1 = (h + 1 + s) / s := by unfold n1; omega
    rw [this]
    simp
  -- the second loop
  have hinb : ∀ j, inBit (inp x h s) (p0 h s + j) ≤ 2 := fun j => inBit_le _ _
  have g8 : CStm.Good (inp x h s) (h + 6) (.loop c2 b2) (S2 x h s 0)
      (S2 x h s (pkLen x.length h s))
      (pkLen x.length h s * (40 * Ex.nodeCost (h + 6) + condCost (h + 6) c2) +
        condCost (h + 6) c2) := by
    refine CStm.Good.loop_const (pkLen x.length h s) (S2 x h s) _ (fun j hj => ?_) ?_
      (fun j hj => ?_) (fun j hj => ?_)
    · have hj' : j < x.length ∨ j < h ∨ j < s ∨ j < 2 ^ ((h + 1 + s) / s) := by
        unfold pkLen at hj; omega
      have hp := inBit_pos x j
      rw [← inBit_inp x h s j] at hp
      simp only [c2, S2, Ex.eval, envP_B, envP_K, envP_H, envP_S, envP_P]
      by_cases h1 : 0 < inBit (inp x h s) (p0 h s + j) <;> by_cases h2 : j < h <;>
        by_cases h3 : j < s <;> by_cases h4 : j < 2 ^ ((h + 1 + s) / s) <;>
        simp only [h1, h2, h3, h4, if_true, if_false] <;> omega
    · have hp := inBit_pos x (pkLen x.length h s)
      rw [← inBit_inp x h s] at hp
      simp only [c2, S2, Ex.eval, envP_B, envP_K, envP_H, envP_S, envP_P]
      have hm1 : x.length ≤ pkLen x.length h s ∧ h ≤ pkLen x.length h s ∧
          s ≤ pkLen x.length h s ∧ 2 ^ ((h + 1 + s) / s) ≤ pkLen x.length h s := by
        unfold pkLen; omega
      simp only [show ¬ pkLen x.length h s < x.length by omega,
        show ¬ pkLen x.length h s < h by omega, show ¬ pkLen x.length h s < s by omega,
        show ¬ pkLen x.length h s < 2 ^ ((h + 1 + s) / s) by omega, if_false,
        show ¬ 0 < inBit (inp x h s) (p0 h s + pkLen x.length h s) by rw [hp]; omega]
    · have hjm : j ≤ 4 * 2 ^ h := le_trans hj hm
      have := hinb j
      simp only [c2, S2, Ex.Fits, Ex.eval, envP_B, envP_K, envP_H, envP_S, envP_P]
      by_cases h1 : 0 < inBit (inp x h s) (p0 h s + j) <;> by_cases h2 : j < h <;>
        by_cases h3 : j < s <;> by_cases h4 : j < 2 ^ ((h + 1 + s) / s) <;>
        simp only [h1, h2, h3, h4, if_true, if_false] <;>
        (repeat' apply And.intro) <;> omega
    · have hjm : j + 1 ≤ 4 * 2 ^ h := le_trans hj hm
      have hb := hinb j
      have hx2 := inBit_x_cases x j
      rw [← inBit_inp x h s j] at hx2
      refine (CStm.Good.seq (CStm.Good.emit ?_) (CStm.Good.seq (CStm.Good.emit ?_)
        (CStm.Good.seq (CStm.Good.set ?_) (CStm.Good.rd rB)))).of_eq ?_ ?_
      · simp only [e1, dbl, S2, Ex.Fits, Ex.eval, envP_B, envP_K, envP_H]
        by_cases h1 : 0 < inBit (inp x h s) (p0 h s + j) <;> by_cases h2 : j < h <;>
          simp only [h1, h2, if_true, if_false] <;> (repeat' apply And.intro) <;> omega
      · simp only [e2, S2, Ex.Fits, Ex.eval, envP_K, envP_S]
        by_cases h3 : j < s <;>
          simp only [h3, if_true, if_false] <;> (repeat' apply And.intro) <;> omega
      · simp only [S2, Ex.Fits, Ex.eval, envP_K]
        repeat' apply And.intro
        all_goals omega
      · have ev1 : e1.eval (S2 x h s j).env = 8 + inBit (inp x h s) (p0 h s + j) / 2 +
            (((if 0 < inBit (inp x h s) (p0 h s + j) then 1 else 0) +
              (if 0 < inBit (inp x h s) (p0 h s + j) then 1 else 0)) +
            (((if j < h then 1 else 0) + (if j < h then 1 else 0)) +
              ((if j < h then 1 else 0) + (if j < h then 1 else 0)))) := rfl
        have ev2 : e2.eval (S2 x h s j).env = 4 + (if j < s then 1 else 0) := rfl
        rw [hx2.1, hx2.2] at ev1
        refine NSt.ext ?_ rfl ?_ ?_
        · show Function.update (Function.update (S2 x h s j).env rK (j + 1)) rB
            (inBit (inp x h s) (min (p0 h s + j + 1) (inp x h s).length)) =
            (S2 x h s (j + 1)).env
          simp only [S2]
          rw [(upd_envP _ _ _ _ _ _ _ _ _).2.2.1, (upd_envP _ _ _ _ _ _ _ _ _).2.2.2, inBit_min,
            show p0 h s + j + 1 = p0 h s + (j + 1) by omega]
        · show min (min (p0 h s + j + 1) (inp x h s).length + 1) (inp x h s).length =
            min (p0 h s + (j + 1) + 1) (inp x h s).length
          omega
        · show (List.range j).flatMap (pkRec x h s) ++ [e1.eval (S2 x h s j).env] ++
            [e2.eval (S2 x h s j).env] = (List.range (j + 1)).flatMap (pkRec x h s)
          rw [ev1, ev2, List.range_succ, List.flatMap_append, List.flatMap_singleton,
            List.append_assoc, List.singleton_append]
          congr 1
          simp only [pkRec]
          by_cases h1 : j < x.length <;> by_cases h2 : j < h <;> by_cases h3 : j < s <;>
            simp [h1, h2, h3] <;> omega
      · simp [Ex.size, e1, e2, dbl]
        have : unitCost (h + 6) ≤ Ex.nodeCost (h + 6) := by
          simp only [Ex.nodeCost]; nlinarith
        omega
  -- assembling
  have G := g1.seq (g2.seq (g3.seq (g4.seq (g5.seq (g6.seq (g7.seq g8))))))
  refine G.mono ?_
  have hc1 : condCost (h + 6) c1 = 7 * Ex.nodeCost (h + 6) + 1 := by
    simp [condCost, c1, Ex.size]
  have hc2 : condCost (h + 6) c2 = 15 * Ex.nodeCost (h + 6) + 1 := by
    simp [condCost, c2, Ex.size]
  have hu : unitCost (h + 6) ≤ Ex.nodeCost (h + 6) := by
    simp only [Ex.nodeCost]; nlinarith
  have hn1 : 1 ≤ Ex.nodeCost (h + 6) := by
    simp only [Ex.nodeCost, unitCost]; nlinarith
  rw [hc1, hc2]
  generalize Ex.nodeCost (h + 6) = nc at hu hn1 ⊢
  generalize unitCost (h + 6) = uc at hu ⊢
  have k1 : n1 h s * (2 * (3 * nc + uc) + (7 * nc + 1)) ≤ 16 * (n1 h s * nc) := by
    have : 2 * (3 * nc + uc) + (7 * nc + 1) ≤ 16 * nc := by omega
    calc _ ≤ n1 h s * (16 * nc) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  have k2 : pkLen x.length h s * (40 * nc + (15 * nc + 1)) ≤
      56 * (pkLen x.length h s * nc) := by
    have : 40 * nc + (15 * nc + 1) ≤ 56 * nc := by omega
    calc _ ≤ pkLen x.length h s * (56 * nc) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  have e1' : ((encodeNat h).length + 1) * (20 * nc) = 20 * ((encodeNat h).length * nc) + 20 * nc :=
    by ring
  have e2' : ((encodeNat s).length + 1) * (20 * nc) = 20 * ((encodeNat s).length * nc) + 20 * nc :=
    by ring
  have e3 : 1000 * nc * ((encodeNat h).length + (encodeNat s).length + n1 h s +
      pkLen x.length h s + 10) = 1000 * ((encodeNat h).length * nc) +
      1000 * ((encodeNat s).length * nc) + 1000 * (n1 h s * nc) +
      1000 * (pkLen x.length h s * nc) + 10000 * nc := by ring
  rw [e1', e2', e3]
  omega


lemma length_encodeNat_le (v : ℕ) : (encodeNat v).length ≤ 2 * v + 1 := by
  rw [CStm.length_encodeNat, Nat.size_eq_bits_len]
  have : Nat.size v ≤ v := by
    rcases Nat.eq_zero_or_pos v with h | h
    · subst h; simp
    · exact Nat.size_le.mpr Nat.lt_two_pow_self
  omega

lemma nodeCost_le (h : ℕ) : Ex.nodeCost (h + 6) ≤ 5184 * (h + 1) ^ 2 := by
  simp only [Ex.nodeCost, unitCost]; nlinarith

end PkParse

open PkParse in
/-- **The machine of the preprocessor.** -/
theorem pkPre_computesWithin : ∃ C : ℕ, ∀ (x : List Bool) (h s : ℕ), 2 ≤ x.length → 2 ≤ h →
    x.length ≤ 2 ^ h → 2 ≤ s → s ≤ h + 2 →
    ComputesWithin (pkPre.machine pkPre.depth) (encodeNats [h, s] ++ x) (pkInput x h s)
      (C * (2 ^ pkWidth x.length h s + h + 2) * (h + 1) ^ 2) := by
  refine ⟨20000 * 5184 + 1000, fun x h s hx hh hxh hs hsh => ?_⟩
  obtain ⟨hPar, hH⟩ := pk_params hx hh hxh hs
  have G := pkPre_good hx hh hxh hs hsh
  have H := CStm.computesWithin (D := pkPre.depth) (x := inp x h s) (w := h + 6) (by omega)
    le_rfl G.1
  rw [G.2.1] at H
  have hout : encodeNats (S2 x h s (pkLen x.length h s)).out = pkInput x h s := rfl
  rw [hout] at H
  refine ComputesWithin.mono H ?_
  have hc := G.2.2
  have hm := pkLen_le hPar.hx hsh
  have hlen : (pkInput x h s).length ≤ 16 * (2 ^ pkWidth x.length h s + h + 2) := by
    rw [length_pkInput]; omega
  have hinp : (inp x h s).length ≤ 2 * h + 2 * s + 2 + x.length := by
    have := PkParse.length_encodeNat_le h
    have := PkParse.length_encodeNat_le s
    simp [inp, encodeNats]; omega
  have hn : x.length ≤ 2 ^ pkWidth x.length h s := hPar.hx.le
  have heh := PkParse.length_encodeNat_le h
  have hes := PkParse.length_encodeNat_le s
  have hn1 : n1 h s ≤ h + 1 := by unfold n1; have := q_le (h := h) (by omega) hs; omega
  have hnc := nodeCost_le h
  set A := 2 ^ pkWidth x.length h s + h + 2 with hA
  set B := (h + 1) ^ 2 with hB
  have hB1 : 1 ≤ B := Nat.one_le_pow _ _ (by omega)
  have hsum : (encodeNat h).length + (encodeNat s).length + n1 h s + pkLen x.length h s + 10 ≤
      20 * A := by omega
  have hcost : 1000 * Ex.nodeCost (h + 6) * ((encodeNat h).length + (encodeNat s).length +
      n1 h s + pkLen x.length h s + 10) ≤ 20000 * 5184 * A * B := by
    calc _ ≤ 1000 * (5184 * B) * (20 * A) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hnc) hsum
      _ = _ := by ring
  have hrest : 20 * ((inp x h s).length + (pkInput x h s).length) + 10 ≤ 1000 * A * B := by
    have : 1000 * A ≤ 1000 * A * B := Nat.le_mul_of_pos_right _ (by omega)
    omega
  calc _ ≤ 20000 * 5184 * A * B + 1000 * A * B := by omega
    _ = _ := by ring

end Lax119563Proofs.Reduction

end Reduction_PkParse
