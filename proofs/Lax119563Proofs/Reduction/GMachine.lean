import Lax119563Proofs.Reduction.GSpec

/-!
# Machines of generators

`Gn.computesWithin`: a generator `g` (independent of the input) whose values fit below
`B` with `2 B ≤ 2 ^ w` gives the deterministic machine `Gn.machine R g`, which computes
`encodeNats (g.out x [])` from `x` within `κ w * g.cost x [] + 20 |…| + 4` steps.
-/

open Lax119563.BinaryEncodings Lax119563.DeterministicTime
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Reduction

variable {R : ℕ} {x : List Bool} {w : ℕ}

namespace Gn

/-- Every `loopX` body is free of `loopX` and `len`. -/
def WFX : Gn → Prop
  | seq g h => WFX g ∧ WFX h
  | ite _ g h => WFX g ∧ WFX h
  | bind _ g => WFX g
  | loop _ g => WFX g
  | loopX _ g => NoX g ∧ WFX g
  | len g => WFX g
  | log _ g => WFX g
  | count g h => WFX g ∧ WFX h
  | _ => True

lemma noX_logS {N : ℕ} (L u v c : Fin N) : (logS L u v c).noX = true := rfl

lemma noX_comp (g : Gn) : ∀ (m : Option ℕ) (A : List ℕ) (d : ℕ), g.NoX →
    (comp R m A d g).noX = true := by
  induction g with
  | skip => intro m A d _; rfl
  | emit e =>
    intro m A d _
    cases m with
    | none => simp [comp, Stm.noX, Xp.noX_comp]
    | some a => rfl
  | seq g h ihg ihh => intro m A d h'; simp [comp, Stm.noX, ihg m A d h'.1, ihh m A d h'.2]
  | ite c g h ihg ihh =>
    intro m A d h'; simp [comp, Stm.noX, Xp.noX_comp, ihg m A d h'.1, ihh m A d h'.2]
  | bind e g ih => intro m A d h'; simp [comp, Stm.noX, Xp.noX_comp, ih m A (d + 1) h']
  | loop lim g ih => intro m A d h'; simp [comp, Stm.noX, Xp.noX_comp, ih m A (d + 2) h']
  | loopX lim g ih => intro m A d h'; exact h'.elim
  | len g ih => intro m A d h'; exact h'.elim
  | log e g ih =>
    intro m A d h'; simp [comp, Stm.noX, Xp.noX_comp, noX_logS, ih m A (d + 1) h']
  | count g h ihg ihh =>
    intro m A d h'
    simp [comp, Stm.noX, ihg (some d) (d :: A) (d + 1) h'.1, ihh m A (d + 1) h'.2]

lemma wr_false {g : Gn} {m : Option ℕ} {A : List ℕ} {d j : ℕ} (hj : j < d) (hjR : j < R)
    (hm : ∀ a, m = some a → a ≠ j) (hmR : ∀ a, m = some a → a < R) :
    Stm.wr (comp R m A d g) (rg R j) = false := by
  refine (wrIn_comp g m A d).wr_false ?_
  rintro (h | ⟨a, ha, he⟩)
  · exact not_above hj hjR h
  · exact hm a ha ((rg_inj (hmR a ha) hjR).mp he.symm)

lemma wf_comp (g : Gn) : ∀ (m : Option ℕ) (A : List ℕ) (d : ℕ), g.WFX → d + g.need ≤ R →
    (∀ a, m = some a → a < d) → (comp R m A d g).WF := by
  induction g with
  | skip => intro m A d _ _ _; trivial
  | emit e =>
    intro m A d _ hR _
    cases m with
    | none => exact ⟨Xp.wf_comp e d hR, trivial⟩
    | some a => trivial
  | seq g h ihg ihh =>
    intro m A d hw hR hm; simp only [need] at hR
    exact ⟨ihg m A d hw.1 (by omega) hm, ihh m A d hw.2 (by omega) hm⟩
  | ite c g h ihg ihh =>
    intro m A d hw hR hm; simp only [need] at hR
    exact ⟨Xp.wf_comp c d (by omega), ihg m A d hw.1 (by omega) hm, ihh m A d hw.2 (by omega) hm⟩
  | bind e g ih =>
    intro m A d hw hR hm; simp only [need] at hR
    exact ⟨Xp.wf_comp e d (by omega), ih m A (d + 1) hw (by omega)
      (fun a ha => by have := hm a ha; omega)⟩
  | loop lim g ih =>
    intro m A d hw hR hm; simp only [need] at hR
    refine ⟨Xp.wf_comp lim d (by omega), rg_ne (by omega) (by omega), ?_, ?_,
      ih m A (d + 2) hw (by omega) (fun a ha => by have := hm a ha; omega)⟩
    · exact wr_false (by omega) (by omega) (fun a ha => by have := hm a ha; omega)
        (fun a ha => by have := hm a ha; omega)
    · exact wr_false (by omega) (by omega) (fun a ha => by have := hm a ha; omega)
        (fun a ha => by have := hm a ha; omega)
  | loopX lim g ih =>
    intro m A d hw hR hm; simp only [need] at hR
    refine ⟨Xp.wf_comp lim d (by omega), rg_ne (by omega) (by omega), rg_ne (by omega) (by omega),
      rg_ne (by omega) (by omega), ?_, ?_, noX_comp g m A (d + 3) hw.1,
      ih m A (d + 3) hw.2 (by omega) (fun a ha => by have := hm a ha; omega)⟩
    · exact wr_false (by omega) (by omega) (fun a ha => by have := hm a ha; omega)
        (fun a ha => by have := hm a ha; omega)
    · exact wr_false (by omega) (by omega) (fun a ha => by have := hm a ha; omega)
        (fun a ha => by have := hm a ha; omega)
  | len g ih =>
    intro m A d hw hR hm; simp only [need] at hR
    exact ⟨trivial, ih m A (d + 1) hw (by omega) (fun a ha => by have := hm a ha; omega)⟩
  | log e g ih =>
    intro m A d hw hR hm; simp only [need] at hR
    have n0 : rg R (d + 3) ≠ rg R d := rg_ne (by omega) (by omega)
    have n2 : rg R (d + 3) ≠ rg R (d + 2) := rg_ne (by omega) (by omega)
    have n1 : rg R (d + 3) ≠ rg R (d + 1) := rg_ne (by omega) (by omega)
    have m0 : rg R (d + 1) ≠ rg R d := rg_ne (by omega) (by omega)
    have m2 : rg R (d + 1) ≠ rg R (d + 2) := rg_ne (by omega) (by omega)
    refine ⟨Xp.wf_comp e d (by omega), ⟨trivial, trivial, trivial, n1, ?_, ?_, ⟨trivial,
      trivial, trivial⟩⟩, ih m A (d + 1) hw (by omega) (fun a ha => by have := hm a ha; omega)⟩
    · simp [Stm.wr, n0, n2]
    · simp [Stm.wr, m0, m2]
  | count g h ihg ihh =>
    intro m A d hw hR hm; simp only [need] at hR
    exact ⟨trivial, ihg (some d) (d :: A) (d + 1) hw.1 (by omega) (fun a ha => by cases ha; omega),
      ihh m A (d + 1) hw.2 (by omega) (fun a ha => by have := hm a ha; omega)⟩

lemma depth_comp (g : Gn) : ∀ (m : Option ℕ) (A : List ℕ) (d : ℕ),
    (comp R m A d g).depth ≤ 3 := by
  induction g with
  | skip => intro m A d; simp [comp, Stm.depth]
  | emit e =>
    intro m A d
    cases m with
    | none =>
      have := Xp.depth_comp (R := R) (d := d) (A := A) e d
      simp only [comp, Stm.depth, Ex.depth]; omega
    | some a => simp [comp, incr, Stm.depth, Ex.depth]
  | seq g h ihg ihh =>
    intro m A d; have := ihg m A d; have := ihh m A d; simp only [comp, Stm.depth]; omega
  | ite c g h ihg ihh =>
    intro m A d; have := ihg m A d; have := ihh m A d
    have := Xp.depth_comp (R := R) (d := d) (A := A) c d
    simp only [comp, Stm.depth, Ex.depth]; omega
  | bind e g ih =>
    intro m A d; have := ih m A (d + 1); have := Xp.depth_comp (R := R) (d := d) (A := A) e d
    simp only [comp, Stm.depth]; omega
  | loop lim g ih =>
    intro m A d; have := ih m A (d + 2)
    have := Xp.depth_comp (R := R) (d := d) (A := A) lim d
    simp only [comp, Stm.depth]; omega
  | loopX lim g ih =>
    intro m A d; have := ih m A (d + 3)
    have := Xp.depth_comp (R := R) (d := d) (A := A) lim d
    simp only [comp, Stm.depth]; omega
  | len g ih => intro m A d; have := ih m A (d + 1); simp only [comp, Stm.depth]; omega
  | log e g ih =>
    intro m A d; have := ih m A (d + 1); have := Xp.depth_comp (R := R) (d := d) (A := A) e d
    simp only [comp, logS, Stm.depth, Ex.depth]; omega
  | count g h ihg ihh =>
    intro m A d; have := ihg (some d) (d :: A) (d + 1); have := ihh m A (d + 1)
    simp only [comp, Stm.depth, Ex.depth]; omega

/-- The machine of a generator. -/
noncomputable def machine (R : ℕ) (g : Gn) : Machine :=
  ((comp R none [] 0 g).code (R + 1) 3).machine

/-- **Machines of generators.** -/
theorem computesWithin {g : Gn} {B : ℕ} (hw : 2 ≤ w) (hB : 2 * B ≤ 2 ^ w) (hR : g.need ≤ R)
    (hwf : g.WFX) (hf : g.Fits x B [])
    (hlen : x.length ≤ (encodeNats (g.out x [])).length) :
    ComputesWithin (machine R g) x (encodeNats (g.out x []))
      (κ w * g.cost x [] + 20 * (encodeNats (g.out x [])).length + 4) := by
  have P : Pre R none [] 0 [] (fun _ => 0) :=
    ⟨rfl, fun i hi => by simp at hi, fun a ha => (by cases ha), fun i hi => by omega⟩
  obtain ⟨G, -⟩ := spec (x := x) hB g none [] 0 [] (fun _ => 0) P (by omega) hf
    (fun a ha => by cases ha)
  exact Stm.computesWithin hw (wf_comp g none [] 0 hwf (by omega) (fun a ha => by cases ha))
    (depth_comp g none [] 0) G hlen

end Gn

end Lax119563Proofs.Reduction
