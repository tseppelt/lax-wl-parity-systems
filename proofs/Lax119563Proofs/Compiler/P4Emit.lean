import Lax119563Proofs.Compiler.P4Edge

/-!
# Pass `P4` (program): the emission of one graph description

Registers and stacks of the location part and the framing of `P4` (`rNt = 4`: the total of
the class sizes, `qSzA = 14`, `qSzB = 15`: the class-size stacks). `p4Emit` emits `n` (from
`rNt`), the colors of the class sizes on `qSzB` (`colorsS`), `m` (from `r4M`) and the edges
on `q4E` in order (`moveAllS q4E qSzA`, `emitAllS qSzA`): **`p4Emit_good`**.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-! ## Registers and stacks of the location part / framing of `P4` -/

/-- The total of the class sizes (kept by the schema part). -/
def rNt : Fin CR := 4
/-- Scratch stack of class sizes. -/
def qSzA : Fin CQ := 14
/-- The class sizes, in order (kept by the schema part). -/
def qSzB : Fin CQ := 15

/-- **The emission**: `n`, colors, `m`, edges. Scratch registers `rT, rP, rJ, rA`. -/
def p4Emit : CStm CR CQ :=
  .seq (.emit (rv rNt)) (.seq (.set rJ (.const 0)) (.seq (colorsS qSzB rT rP rJ rA)
    (.seq (.emit (rv r4M)) (.seq (moveAllS q4E qSzA rT rP) (emitAllS qSzA rT rP)))))

/-- The words of a graph description with class sizes `L` and edges `Es`. -/
def descOf (L : List ℕ) (Es : List (ℕ × ℕ)) : List ℕ :=
  L.sum :: colorsOf 0 L ++ Es.length :: Es.flatMap fun e => [e.1, e.2]

lemma p4Emit_arith {N U a b c : ℕ} (hU : U ≤ N) (hU' : 64 ≤ U) :
    2 * N + U + (2 * N + U + ((2 * U + 1) + ((a + b + 1) * (30 * N) + (2 * N + U +
      ((c + 1) * (10 * N) + (c + 1) * (10 * N)))))) ≤ (a + b + 2 * c + 8) * (40 * N) := by
  nlinarith

/-- **The emission.** -/
lemma p4Emit_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (st : NSt CR CQ) (L : List ℕ)
    (Es : List (ℕ × ℕ)) (hb : st.Bdd w) (hp : st.pos ≤ x.length) (hB : st.stk qSzB = L)
    (hE : st.stk q4E = pairsRev Es) (hA : st.stk qSzA = []) (hN : st.env rNt = L.sum)
    (hM : st.env r4M = Es.length) :
    ∃ st', Good x w p4Emit st st'
        ((L.length + L.sum + 2 * Es.length + 8) * (40 * Ex.nodeCost w)) ∧
      st'.out = st.out ++ descOf L Es ∧
      st'.stk = Function.update (Function.update st.stk qSzB []) q4E [] ∧
      st'.pos = st.pos ∧
      ∀ r, r ≠ rT → r ≠ rP → r ≠ rJ → r ≠ rA → st'.env r = st.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hNw : L.sum < 2 ^ w := by rw [← hN]; exact hb.1 _
  have hMw : st.env r4M < 2 ^ w := hb.1 _
  have r1 := Good.emit (x := x) (w := w) (st := st) (e := rv rNt) (hb.1 _)
  set s1 : NSt CR CQ := { st with out := st.out ++ [(rv rNt : Ex CR).eval st.env] }
  have r2 := Good.set (x := x) (w := w) (st := s1) (r := rJ) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  set s2 := s1.set rJ ((Ex.const 0 : Ex CR).eval s1.env)
  have r3 := Good.sne (x := x) (w := w) (st := s2) rP qSzB
  set s3 := s2.set rP (if (s2.stk qSzB).isEmpty then 0 else 1)
  have e3B : s3.stk qSzB = L := hB
  have e3f : s3.env rP = if L = [] then 0 else 1 := by
    simp only [s3, NSt.set_env, Function.update_self]
    rw [show s2.stk qSzB = L from hB]; cases L <;> rfl
  have e3p : s3.env rJ = 0 := by
    simp [s3, s2, Ex.eval, Function.update_of_ne (show rJ ≠ rP by decide)]
  obtain ⟨s4, r4, h4s, h4p, h4o, h4P, h4e⟩ := colorsS_loop_good (x := x) hw
    (t := rT) (f := rP) (p := rJ) (i := rA) (q := qSzB) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) L s3 e3B e3f (by rw [e3p]; omega)
  have e4M : s4.env r4M = st.env r4M := by
    rw [h4e _ (by decide) (by decide) (by decide) (by decide)]
    simp [s3, s2, s1, Function.update_of_ne (show r4M ≠ rP by decide),
      Function.update_of_ne (show r4M ≠ rJ by decide)]
  have r5 := Good.emit (x := x) (w := w) (st := s4) (e := rv r4M)
    (by show s4.env r4M < 2 ^ w; rw [e4M]; exact hMw)
  set s5 : NSt CR CQ := { s4 with out := s4.out ++ [(rv r4M : Ex CR).eval s4.env] }
  have r15 := r1.seq (r2.seq (r3.seq (r4.seq r5)))
  have hb5 := r15.bdd hw hb hp
  obtain ⟨s6, r6, h6s, h6p, h6o, h6e⟩ := moveAllS_good (x := x) hw (q := q4E) (q' := qSzA)
    (t := rT) (f := rP) (by decide) (by decide) s5 hb5.1
  have hb6 := r6.bdd hw hb5.1 hb5.2
  obtain ⟨s7, r7, h7s, h7p, h7o, h7e⟩ := emitAllS_good (x := x) hw (q := qSzA) (t := rT)
    (f := rP) (by decide) s6 hb6.1
  have e5s : s5.stk = Function.update st.stk qSzB [] := by
    show s4.stk = _; rw [h4s]; rfl
  have e6A : s6.stk qSzA = Es.flatMap fun e => [e.1, e.2] := by
    rw [h6s, Function.update_self, e5s]
    simp [Function.update_of_ne (show q4E ≠ qSzB by decide),
      Function.update_of_ne (show qSzA ≠ qSzB by decide), hA, hE, pairsRev]
  have e6E : (s5.stk q4E).length = 2 * Es.length := by
    rw [e5s, Function.update_of_ne (by decide), hE, pairsRev, List.length_reverse,
      List.length_flatMap]
    simp [sum_map_const]; ring
  refine ⟨s7, (r1.seq (r2.seq ((r3.seq r4).seq (r5.seq (r6.seq r7))))).mono ?_, ?_, ?_, ?_, ?_⟩
  · have hl : (Es.flatMap fun e => [e.1, e.2]).length = 2 * Es.length := by
      induction Es with
      | nil => rfl
      | cons a l ih => simp [ih]; ring
    rw [e6A, e6E, hl]
    simp only [rv, Ex.size]
    generalize Ex.nodeCost w = N at *
    generalize unitCost w = U at *
    have := p4Emit_arith (N := N) (U := U) (a := L.length) (b := L.sum) (c := 2 * Es.length) hU hU'
    nlinarith
  · rw [h7o, e6A, h6o]
    show s4.out ++ [s4.env r4M] ++ _ = _
    rw [h4o, e4M, e3p, hM]
    simp [s3, s2, s1, descOf, Ex.eval, rv, hN]
  · rw [h7s, h6s, e5s]
    funext q
    by_cases hqA : q = qSzA
    · subst hqA; simp [Function.update_of_ne (show qSzA ≠ q4E by decide),
        Function.update_of_ne (show qSzA ≠ qSzB by decide), hA]
    · rw [Function.update_of_ne hqA, Function.update_of_ne hqA]
  · rw [h7p, h6p]; show s4.pos = _; rw [h4p]; rfl
  · intro r h1 h2 h3 h4
    rw [h7e r h1 h2, h6e r h1 h2]
    show s4.env r = _
    rw [h4e r h1 h2 h3 h4]
    simp [s3, s2, s1, Function.update_of_ne h2, Function.update_of_ne h3]

end Lax119563Proofs.Compiler
