import Lax119563Proofs.Machines.Output
import Lax119563Proofs.Main.ComposeMain

/-!
# Simulating a machine of the model inside a structured machine

For a deterministic machine `D` of the model, `simTM D` is a structured machine
(`Machines.TM`) on the tapes of `D` plus a marker tape. It simulates `D` step by step; the head
of the marker tape (which holds a single mark at the origin) moves together with the head of
tape `0`, and the control state remembers on which side of the origin that head is. When `D`
halts, the head of tape `0` is moved back to the origin. So if `D` computes `z` from `y`
within `t` steps, `simTM D` ends within `2 t` transitions with `z` on tape `0` as a word tape
with the head on position `0` (`simTM_runsWithin`).

The length of an output is bounded by the length of the input plus the running time
(`length_le_of_computesWithin`).
-/

open Lax489179.TuringMachine (Machine Config Move Instruction init step run Deterministic)
open Lax119563.DeterministicTime

namespace Lax119563Proofs.Hardness

open Machines

/-- The symbols of a machine with `m + 3` symbols as a tape alphabet: blank `0`, bits `1, 2`. -/
instance finAlphabet (m : ℕ) : TapeAlphabet (Fin (m + 3)) where
  blank := 0
  bit b := if b then 2 else 1
  bit_injective := by
    intro a b h
    cases a <;> cases b <;> simp_all [Fin.ext_iff, Nat.mod_eq_of_lt (show 2 < m + 3 by omega),
      Nat.mod_eq_of_lt (show 1 < m + 3 by omega)]
  bit_ne_blank := by
    intro b
    cases b <;> simp [Fin.ext_iff, Nat.mod_eq_of_lt (show 2 < m + 3 by omega)]

lemma one_ne_zero_fin (m : ℕ) : (1 : Fin (m + 3)) ≠ 0 :=
  TapeAlphabet.bit_ne_blank (Γ := Fin (m + 3)) false

lemma two_ne_zero_fin (m : ℕ) : (2 : Fin (m + 3)) ≠ 0 :=
  TapeAlphabet.bit_ne_blank (Γ := Fin (m + 3)) true

/-! ## Output length -/

theorem tape_zero_blank (M : Machine) (x : List Bool) (t : ℕ) (z : ℤ)
    (hz : (x.length : ℤ) + t ≤ z) : (runOn M x t).tape 0 z = 0 := by
  induction t generalizing z with
  | zero =>
    simp only [runOn, run, init]
    have : x[z.toNat]? = none := List.getElem?_eq_none (by omega)
    simp [this]
  | succ t ih =>
    rw [Main.runOn_succ]
    have hh := Main.Compose.head_natAbs_le M x 0 t
    unfold step
    rcases (runOn M x t).answer with _ | b
    · dsimp only
      split
      · exact ih z (by omega)
      · dsimp only
        rw [if_neg (by omega)]
        exact ih z (by omega)
    · exact ih z (by omega)

/-- **The output is not longer than the input plus the running time.** -/
theorem length_le_of_computesWithin {M : Machine} {x y : List Bool} {t : ℕ}
    (h : ComputesWithin M x y t) : y.length ≤ x.length + t := by
  by_contra hlt
  push Not at hlt
  have h0 := tape_zero_blank M x t ((x.length + t : ℕ) : ℤ) (by push_cast; omega)
  rw [h.2] at h0
  simp only [init, Int.toNat_natCast, List.getElem?_eq_getElem hlt] at h0
  rw [if_pos ⟨trivial, by omega⟩] at h0
  revert h0
  cases y[x.length + t]
  · exact one_ne_zero_fin _
  · exact two_ne_zero_fin _

/-! ## The simulating machine -/

variable (D : Machine)

/-- The marker tape. -/
def mkI : Fin (D.tapes + 2) := Fin.last (D.tapes + 1)

/-- The mark at the origin. -/
def mark : Fin (D.symbols + 3) := bit false

/-- The cells of the marker tape. -/
def markCells : ℤ → Fin (D.symbols + 3) := listCells [mark D]

lemma markCells_eq_mark_iff (z : ℤ) : markCells D z = mark D ↔ z = 0 := by
  unfold markCells listCells
  constructor
  · intro h
    by_contra hz
    split_ifs at h with h0
    · have : [mark D][z.toNat]? = none := List.getElem?_eq_none (by simp; omega)
      rw [this] at h
      exact (TapeAlphabet.bit_ne_blank (Γ := Fin (D.symbols + 3)) false) h.symm
    · exact (TapeAlphabet.bit_ne_blank (Γ := Fin (D.symbols + 3)) false) h.symm
  · rintro rfl; simp

/-- Whether a move goes right. -/
def isRight : Move → Bool
  | .right => true
  | _ => false

/-- The direction of the rewinding moves. -/
def dir (sg : Bool) : Move := if sg then .left else .right

lemma castSucc_ne_mkI (j : Fin (D.tapes + 1)) : j.castSucc ≠ mkI D :=
  Fin.castSucc_ne_last j

lemma zero_ne_mkI : (0 : Fin (D.tapes + 2)) ≠ mkI D := by
  simpa using castSucc_ne_mkI D 0

/-- The simulating machine. States `inl (q, sg)` simulate `D` in state `q`, with `sg` the
side of the origin of the head of tape `0` (`true`: right); states `inr sg` rewind. -/
def simTM : TM (D.tapes + 2) (Fin (D.symbols + 3)) where
  Q := (Fin (D.states + 1) × Bool) ⊕ Bool
  start := .inl (0, true)
  δ
    | .inl (q, sg), s =>
      match D.transition q (fun j => s j.castSucc) false with
      | .halt _ => some (.inr sg, s, fun _ => .stay)
      | .next q' w m =>
        some (.inl (q', if s (mkI D) = mark D then isRight (m 0) else sg),
          Fin.lastCases (motive := fun _ => Fin (D.symbols + 3)) (s (mkI D)) w,
          Fin.lastCases (motive := fun _ => Move) (m 0) m)
    | .inr sg, s =>
      if s (mkI D) = mark D then none
      else some (.inr sg, s, Fin.lastCases (motive := fun _ => Move) (dir sg)
        (fun j => if j = 0 then dir sg else .stay))

variable {D}

/-- The rewinding phase: the head of tape `0` and of the marker tape are on position `±d`
(the sign given by `sg`), and they move back to the origin in `d` transitions. -/
theorem rew_haltsFrom : ∀ (d : ℕ) (T : Machines.Tapes (D.tapes + 2) (Fin (D.symbols + 3)))
    (sg : Bool), T (mkI D) = ⟨(T 0).head, markCells D⟩ →
    ((T 0).head = d ∧ sg = true ∨ (T 0).head = -d ∧ sg = false) →
    (simTM D).HaltsFrom (.inr sg) T d
      (Function.update (Function.update T 0 ⟨0, (T 0).cells⟩) (mkI D) ⟨0, markCells D⟩) := by
  intro d
  induction d with
  | zero =>
    intro T sg hmk hsg
    have h0 : (T 0).head = 0 := by omega
    have hT : Function.update (Function.update T 0 ⟨0, (T 0).cells⟩) (mkI D)
        ⟨0, markCells D⟩ = T := by
      funext i
      by_cases hi : i = mkI D
      · subst hi; rw [Function.update_self, hmk, h0]
      · rw [Function.update_of_ne hi]
        by_cases hi0 : i = 0
        · subst hi0; rw [Function.update_self, ← h0]
        · rw [Function.update_of_ne hi0]
    rw [hT]
    refine .halt ?_
    have : readAll T (mkI D) = mark D := by
      simp only [readAll, Tape.read, hmk, h0, markCells_eq_mark_iff]
    simp [simTM, this]
  | succ d ih =>
    intro T sg hmk hsg
    have hne : (T 0).head ≠ 0 := by omega
    have hread : readAll T (mkI D) ≠ mark D := by
      simp only [readAll, Tape.read, hmk, ne_eq, markCells_eq_mark_iff]; exact hne
    set mv : Fin (D.tapes + 2) → Move := Fin.lastCases (motive := fun _ => Move) (dir sg)
        (fun j => if j = 0 then dir sg else .stay) with hmv
    have hδ : (simTM D).δ (.inr sg) (readAll T) = some (.inr sg, readAll T, mv) := by
      show (if readAll T (mkI D) = mark D then none else some _) = _
      rw [if_neg hread]
      rfl
    have hmv0 : mv 0 = dir sg := by
      have : (0 : Fin (D.tapes + 2)) = (0 : Fin (D.tapes + 1)).castSucc := rfl
      rw [this, hmv, Fin.lastCases_castSucc]; simp
    have hmvm : mv (mkI D) = dir sg := by rw [hmv, mkI, Fin.lastCases_last]
    have hmvo : ∀ i, i ≠ 0 → i ≠ mkI D → mv i = .stay := by
      intro i hi0 him
      induction i using Fin.lastCases with
      | last => exact absurd rfl him
      | cast j =>
        rw [hmv, Fin.lastCases_castSucc]
        have : j ≠ 0 := by rintro rfl; exact hi0 rfl
        simp [this]
    set T₁ := applyAll T (readAll T) mv with hT₁
    have hT₁i : ∀ i, T₁ i = (T i).move (mv i) := fun i => Tape.act_read _ _
    have hoff : (dir sg).offset = if sg then -1 else 1 := by
      cases sg <;> rfl
    have h₁0 : T₁ 0 = ⟨(T 0).head + (dir sg).offset, (T 0).cells⟩ := by
      rw [hT₁i, hmv0]; rfl
    have h₁m : T₁ (mkI D) = ⟨(T₁ 0).head, markCells D⟩ := by
      rw [hT₁i, hmvm, h₁0, hmk]; rfl
    have hsg₁ : (T₁ 0).head = d ∧ sg = true ∨ (T₁ 0).head = -d ∧ sg = false := by
      rw [h₁0]
      rcases hsg with ⟨h, rfl⟩ | ⟨h, rfl⟩
      · left; refine ⟨?_, rfl⟩
        show (T 0).head + -1 = (d : ℤ)
        push_cast at h; omega
      · right; refine ⟨?_, rfl⟩
        show (T 0).head + 1 = -(d : ℤ)
        push_cast at h; omega
    have := ih T₁ sg h₁m hsg₁
    have hfin : Function.update (Function.update T₁ 0 ⟨0, (T₁ 0).cells⟩) (mkI D)
        ⟨0, markCells D⟩ =
        Function.update (Function.update T 0 ⟨0, (T 0).cells⟩) (mkI D) ⟨0, markCells D⟩ := by
      funext i
      by_cases hi : i = mkI D
      · subst hi; simp
      · rw [Function.update_of_ne hi, Function.update_of_ne hi]
        by_cases hi0 : i = 0
        · subst hi0; simp [h₁0]
        · rw [Function.update_of_ne hi0, Function.update_of_ne hi0, hT₁i, hmvo i hi0 hi]
          simp [Tape.move]
    rw [hfin] at this
    rw [show d + 1 = d + 1 from rfl]
    exact .step hδ this

/-- The simulation invariant between a configuration of `D` and the tapes of `simTM D`. -/
structure Rel (c : Config D) (sg : Bool) (T : Machines.Tapes (D.tapes + 2) (Fin (D.symbols + 3))) :
    Prop where
  tapes : ∀ j : Fin (D.tapes + 1), T j.castSucc = ⟨c.head j, c.tape j⟩
  mkt : T (mkI D) = ⟨c.head 0, markCells D⟩
  pos : 0 < c.head 0 → sg = true
  neg : c.head 0 < 0 → sg = false

lemma Rel.read {c : Config D} {sg : Bool} {T : Machines.Tapes (D.tapes + 2) (Fin (D.symbols + 3))}
    (h : Rel c sg T) : (fun j : Fin (D.tapes + 1) => readAll T j.castSucc) =
      fun j => c.tape j (c.head j) := by
  funext j; simp [readAll, Tape.read, h.tapes j]

lemma Rel.tape0 {c : Config D} {sg : Bool} {T : Machines.Tapes (D.tapes + 2) (Fin (D.symbols + 3))}
    (h : Rel c sg T) : T 0 = ⟨c.head 0, c.tape 0⟩ := h.tapes 0

theorem sim_haltsFrom : ∀ (t : ℕ) (c : Config D) (sg : Bool)
    (T : Machines.Tapes (D.tapes + 2) (Fin (D.symbols + 3))),
    c.answer = none → Rel c sg T → (run D t (fun _ => false) c).answer.isSome →
    ∃ t' ≤ t + ((run D t (fun _ => false) c).head 0).natAbs, ∃ T',
      (simTM D).HaltsFrom (.inl (c.state, sg)) T t' T' ∧
        T' 0 = ⟨0, (run D t (fun _ => false) c).tape 0⟩ := by
  intro t
  induction t with
  | zero => intro c sg T hc _ h; simp [run, hc] at h
  | succ t ih =>
    intro c sg T hc hR h
    rw [TM.run_succ_false] at h ⊢
    have hread := hR.read
    rcases htr : D.transition c.state (fun j => c.tape j (c.head j)) false with b | ⟨q', w, m⟩
    · -- `D` halts: rewind
      have hs : step D false c = { c with answer := some b } := by simp [step, hc, htr]
      rw [hs, Main.run_false_of_halted _ _ _ (by simp)]
      have hδ : (simTM D).δ (.inl (c.state, sg)) (readAll T) =
          some (.inr sg, readAll T, fun _ => .stay) := by
        simp only [simTM]; rw [hread, htr]
      have hT0 := hR.tape0
      have hrew := rew_haltsFrom (c.head 0).natAbs T sg (by rw [hR.mkt, hT0])
        (by
          rw [hT0]
          dsimp only
          rcases lt_trichotomy (c.head 0) 0 with hl | hl | hl
          · right; exact ⟨by omega, hR.neg hl⟩
          · cases sg
            · right; exact ⟨by omega, rfl⟩
            · left; exact ⟨by omega, rfl⟩
          · left; exact ⟨by omega, hR.pos hl⟩)
      refine ⟨(c.head 0).natAbs + 1, by simp,
        Function.update (Function.update T 0 ⟨0, (T 0).cells⟩) (mkI D) ⟨0, markCells D⟩,
        .step hδ (by simpa using hrew), ?_⟩
      rw [Function.update_of_ne (zero_ne_mkI D), Function.update_self, hT0]
    · have hs : step D false c = ⟨q', fun j => c.head j + (m j).offset,
          fun j z => if z = c.head j then w j else c.tape j z, none⟩ := by
        simp [step, hc, htr]
      rw [hs] at h ⊢
      set sg' := if readAll T (mkI D) = mark D then isRight (m 0) else sg with hsg'
      set W := Fin.lastCases (motive := fun _ => Fin (D.symbols + 3)) (readAll T (mkI D)) w
      set Mv := Fin.lastCases (motive := fun _ => Move) (m 0) m
      have hδ : (simTM D).δ (.inl (c.state, sg)) (readAll T) = some (.inl (q', sg'), W, Mv) := by
        simp only [simTM]; rw [hread, htr]
      have hR' : Rel ⟨q', fun j => c.head j + (m j).offset,
          fun j z => if z = c.head j then w j else c.tape j z, none⟩ sg' (applyAll T W Mv) := by
        have hmkread : readAll T (mkI D) = markCells D (c.head 0) := by
          simp [readAll, Tape.read, hR.mkt]
        refine ⟨fun j => ?_, ?_, ?_, ?_⟩
        · simp only [applyAll, W, Mv, Fin.lastCases_castSucc, hR.tapes j, Tape.act]
          congr 1
          funext z; simp [Function.update_apply]
        · simp only [applyAll, W, Mv, mkI, Fin.lastCases_last]
          rw [show Fin.last (D.tapes + 1) = mkI D from rfl, hR.mkt]
          simp only [Tape.act, Tape.mk.injEq, true_and]
          funext z
          rw [Function.update_apply]
          split_ifs with hz
          · subst hz; simp [readAll, Tape.read, hR.mkt]
          · rfl
        · intro hpos
          dsimp only at hpos
          simp only [hsg', hmkread, markCells_eq_mark_iff]
          split_ifs with h0
          · have := Main.Compose.offset_bound (m 0)
            rcases hm : m 0 <;> simp_all [Move.offset, isRight]
          · exact hR.pos (by have := Main.Compose.offset_bound (m 0); omega)
        · intro hneg
          dsimp only at hneg
          simp only [hsg', hmkread, markCells_eq_mark_iff]
          split_ifs with h0
          · have := Main.Compose.offset_bound (m 0)
            rcases hm : m 0 <;> simp_all [Move.offset, isRight]
          · exact hR.neg (by have := Main.Compose.offset_bound (m 0); omega)
      obtain ⟨t', ht', T', hH, hT'⟩ := ih _ sg' _ rfl hR' h
      exact ⟨t' + 1, by omega, T', .step hδ hH, hT'⟩

end Lax119563Proofs.Hardness
