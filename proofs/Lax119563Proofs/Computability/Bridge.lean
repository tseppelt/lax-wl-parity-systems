import Lax119563Proofs.Computability.SimSpec
import Lax119563.ParameterizedComplexity

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
