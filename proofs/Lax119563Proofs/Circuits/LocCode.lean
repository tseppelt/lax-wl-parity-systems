import Lax119563Proofs.Circuits.Verifier

/-!
# Numbering the locations

An explicit injective numbering `Loc.code : Loc M H → Fin (numLoc M H)` of the verifier's
locations with `numLoc M H = 16 * (H + cM M) ^ 5`: a location is a tag `< 16` and at most five
fields, each a number below `H + cM M`, written in mixed radix.
-/

namespace Lax119563Proofs.Circuits

open Lax489179.TuringMachine

variable {M : Machine} {H : ℕ}

/-- Two digits in radix `F`. -/
def pack (F a b : ℕ) : ℕ := a + F * b

lemma pack_inj {F a b a' b' : ℕ} (ha : a < F) (ha' : a' < F) (h : pack F a b = pack F a' b') :
    a = a' ∧ b = b' := by
  unfold pack at h
  have hF : 0 < F := by omega
  have h1 : (a + F * b) % F = (a' + F * b') % F := by rw [h]
  have h2 : (a + F * b) / F = (a' + F * b') / F := by rw [h]
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt ha'] at h1
  rw [Nat.add_mul_div_left _ _ hF, Nat.add_mul_div_left _ _ hF, Nat.div_eq_of_lt ha,
    Nat.div_eq_of_lt ha'] at h2
  omega

lemma pack_lt {F a b G : ℕ} (ha : a < F) (hb : b < G) : pack F a b < F * G := by
  unfold pack
  have : F * b + F ≤ F * G := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hb
  omega

/-- The number of an option of a Boolean. -/
def encOpt : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

lemma encOpt_lt (b : Option Bool) : encOpt b < 3 := by
  rcases b with _ | _ | _ <;> simp [encOpt]

lemma encOpt_inj {b b' : Option Bool} (h : encOpt b = encOpt b') : b = b' := by
  rcases b with _ | _ | _ <;> rcases b' with _ | _ | _ <;> simp_all [encOpt]

/-- The number of a cell value. -/
def encCV (c : CellVal M) : ℕ := pack 2 (if c.2 then 1 else 0) c.1.val

/-- The number of an extended state. -/
def encExt (p : ExtState M) : ℕ := pack 3 (encOpt p.2) p.1.val

/-- The number of a row. -/
def encRow (ρ : Row M) : ℕ :=
  pack (3 * (M.states + 1)) (encExt ρ.1)
    (pack (2 ^ (M.tapes + 1)) (finFunctionFinEquiv ρ.2.1).val (finFunctionFinEquiv ρ.2.2).val)

lemma encCV_lt (c : CellVal M) : encCV c < 2 * (M.symbols + 3) :=
  pack_lt (by split_ifs <;> omega) c.1.isLt

lemma encExt_lt (p : ExtState M) : encExt p < 3 * (M.states + 1) :=
  pack_lt (encOpt_lt _) p.1.isLt

/-- The number of rows. -/
def rowBound (M : Machine) : ℕ :=
  3 * (M.states + 1) * (2 ^ (M.tapes + 1) * (M.symbols + 3) ^ (M.tapes + 1))

lemma encRow_lt (ρ : Row M) : encRow ρ < rowBound M :=
  pack_lt (encExt_lt _) (pack_lt (finFunctionFinEquiv ρ.2.1).isLt
    (finFunctionFinEquiv ρ.2.2).isLt)

lemma encCV_inj {c c' : CellVal M} (h : encCV c = encCV c') : c = c' := by
  obtain ⟨h1, h2⟩ := pack_inj (by split_ifs <;> omega) (by split_ifs <;> omega) h
  refine Prod.ext (Fin.ext h2) ?_
  revert h1; cases c.2 <;> cases c'.2 <;> simp

lemma encExt_inj {p p' : ExtState M} (h : encExt p = encExt p') : p = p' := by
  obtain ⟨h1, h2⟩ := pack_inj (encOpt_lt _) (encOpt_lt _) h
  exact Prod.ext (Fin.ext h2) (encOpt_inj h1)

lemma encRow_inj {ρ ρ' : Row M} (h : encRow ρ = encRow ρ') : ρ = ρ' := by
  obtain ⟨h1, h2⟩ := pack_inj (encExt_lt _) (encExt_lt _) h
  obtain ⟨h3, h4⟩ := pack_inj (finFunctionFinEquiv ρ.2.1).isLt
    (finFunctionFinEquiv ρ'.2.1).isLt h2
  have e1 := encExt_inj h1
  have e2 := finFunctionFinEquiv.injective (Fin.ext h3)
  have e3 := finFunctionFinEquiv.injective (Fin.ext h4)
  obtain ⟨a, b, c⟩ := ρ
  obtain ⟨a', b', c'⟩ := ρ'
  simp_all

/-- The bound on all constant-size fields. -/
def cM (M : Machine) : ℕ := 9 + (M.tapes + 2) + 2 * (M.symbols + 3) + rowBound M

/-- The radix of the location numbers. -/
def radix (M : Machine) (H : ℕ) : ℕ := H + 1 + cM M

/-- The tag and five fields of a location. -/
def Loc.tuple : Loc M H → ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
  | .accept => (0, 0, 0, 0, 0, 0)
  | .reject => (1, 0, 0, 0, 0, 0)
  | .query => (2, 0, 0, 0, 0, 0)
  | .cell d θ ν c => (3, d, θ, ν, encCV c, 0)
  | .state d θ p => (4, d, θ, encExt p, 0, 0)
  | .headIn d θ ν u => (5, d, θ, ν, u, 0)
  | .headSet d θ ν β => (6, d, θ, ν, β, 0)
  | .restore d θ ν c β => (7, d, θ, ν, encCV c, β)
  | .gather d θ ν c β => (8, d, θ, ν, encCV c, β)
  | .baseCell ν ρ old k => (9, ν, encRow ρ, encCV old, k, 0)
  | .baseState ρ k => (10, encRow ρ, k, 0, 0, 0)
  | .setJ ν h c => (11, ν, h, encCV c, 0, 0)

lemma Loc.tuple_injective : Function.Injective (Loc.tuple (M := M) (H := H)) := by
  intro L L' h
  cases L <;> cases L' <;> simp only [Loc.tuple, Prod.mk.injEq] at h <;>
    (try omega) <;>
    (try simp only [Loc.cell.injEq, Loc.state.injEq, Loc.headIn.injEq, Loc.headSet.injEq,
      Loc.restore.injEq, Loc.gather.injEq, Loc.baseCell.injEq, Loc.baseState.injEq,
      Loc.setJ.injEq]) <;>
    (try exact ⟨Fin.ext h.2.1, Fin.ext h.2.2.1, Fin.ext h.2.2.2.1, encCV_inj h.2.2.2.2.1⟩) <;>
    (try exact ⟨Fin.ext h.2.1, Fin.ext h.2.2.1, encExt_inj h.2.2.2.1⟩) <;>
    (try exact ⟨Fin.ext h.2.1, Fin.ext h.2.2.1, Fin.ext h.2.2.2.1, Fin.ext h.2.2.2.2.1⟩) <;>
    (try exact ⟨Fin.ext h.2.1, Fin.ext h.2.2.1, Fin.ext h.2.2.2.1, encCV_inj h.2.2.2.2.1,
      Fin.ext h.2.2.2.2.2⟩) <;>
    (try exact ⟨Fin.ext h.2.1, encRow_inj h.2.2.1, encCV_inj h.2.2.2.1, Fin.ext h.2.2.2.2.1⟩) <;>
    (try exact ⟨encRow_inj h.2.1, Fin.ext h.2.2.1⟩) <;>
    (try exact ⟨Fin.ext h.2.1, Fin.ext h.2.2.1, encCV_inj h.2.2.2.1⟩)

lemma Loc.tuple_lt (L : Loc M H) :
    L.tuple.1 < 16 ∧ L.tuple.2.1 < radix M H ∧ L.tuple.2.2.1 < radix M H ∧
      L.tuple.2.2.2.1 < radix M H ∧ L.tuple.2.2.2.2.1 < radix M H ∧
      L.tuple.2.2.2.2.2 < radix M H := by
  have hcv : ∀ c : CellVal M, encCV c < radix M H := fun c => by
    have := encCV_lt c; unfold radix cM; omega
  have hex : ∀ p : ExtState M, encExt p < radix M H := fun p => by
    have := encExt_lt p
    have : 3 * (M.states + 1) ≤ rowBound M := by
      unfold rowBound
      exact Nat.le_mul_of_pos_right _ (by positivity)
    unfold radix cM; omega
  have hrw : ∀ ρ : Row M, encRow ρ < radix M H := fun ρ => by
    have := encRow_lt ρ; unfold radix cM; omega
  have hd : ∀ d : Fin (H + 1), d.val < radix M H := fun d => by
    have := d.isLt; unfold radix; omega
  have hk : ∀ {m : ℕ} (k : Fin m), m ≤ 9 + (M.tapes + 2) → k.val < radix M H := fun k hm => by
    have := k.isLt; unfold radix cM; omega
  have h0 : 0 < radix M H := by unfold radix; omega
  cases L <;> simp only [Loc.tuple] <;>
    refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | exact h0
    | exact hd _
    | exact hcv _
    | exact hex _
    | exact hrw _
    | exact hk _ (by omega)

/-- The number of location codes. -/
def numLoc (M : Machine) (H : ℕ) : ℕ := 16 * radix M H ^ 5

/-- The number of a location. -/
def Loc.code (L : Loc M H) : Fin (numLoc M H) :=
  ⟨pack 16 L.tuple.1 (pack (radix M H) L.tuple.2.1 (pack (radix M H) L.tuple.2.2.1
    (pack (radix M H) L.tuple.2.2.2.1 (pack (radix M H) L.tuple.2.2.2.2.1
      L.tuple.2.2.2.2.2)))), by
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := L.tuple_lt
    have := pack_lt h0 (pack_lt h1 (pack_lt h2 (pack_lt h3 (pack_lt h4 h5))))
    unfold numLoc
    calc _ < _ := this
      _ = _ := by ring⟩

lemma Loc.code_injective : Function.Injective (Loc.code (M := M) (H := H)) := by
  intro L L' h
  have h' := congrArg Fin.val h
  simp only [Loc.code] at h'
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := L.tuple_lt
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := L'.tuple_lt
  obtain ⟨e0, h'⟩ := pack_inj a0 b0 h'
  obtain ⟨e1, h'⟩ := pack_inj a1 b1 h'
  obtain ⟨e2, h'⟩ := pack_inj a2 b2 h'
  obtain ⟨e3, h'⟩ := pack_inj a3 b3 h'
  obtain ⟨e4, e5⟩ := pack_inj a4 b4 h'
  apply Loc.tuple_injective
  ext <;> assumption

end Lax119563Proofs.Circuits
