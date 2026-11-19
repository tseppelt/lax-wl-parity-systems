import Lax119563Proofs.Compiler.PEmitHub
import Lax119563Proofs.Compiler.CColors
import Lax119563Proofs.Compiler.CFrame

/-!
# Pass `P4` (program): pushing edges

Edges are pushed on the stack `q4E` (first `u`, then `v`, so that the stack holds the edges
reversed) and counted in `r4M` (`EdgeEff`). `pE h v` pushes one edge (`pE_good`); `cposS`
computes the optional position of a coordinate slot from the answer data `(off, mode)` with
`mode = 2` for two labels and `mode = ε · seed` for one label (`cposS_good`, matching
`cposA`); `pEo h f v` pushes `(h, v)` if the flag `f` is set (`pEo_good`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

open CStm

/-! ## Registers and stacks of `P4` -/

/-- The edge stack. -/
def q4E : Fin CQ := 1
def r4Eps : Fin CR := 35
/-- The edge count. -/
def r4M : Fin CR := 36
/-- A computed flag and value (optional position). -/
def r4F : Fin CR := 21
def r4V : Fin CR := 22

/-! ## Edge effects -/

/-- The words of a list of edges on the stack (reversed). -/
def pairsRev (Es : List (ℕ × ℕ)) : List ℕ := (Es.flatMap fun e => [e.1, e.2]).reverse

lemma pairsRev_append (E₁ E₂ : List (ℕ × ℕ)) : pairsRev (E₁ ++ E₂) = pairsRev E₂ ++ pairsRev E₁ := by
  simp [pairsRev]

/-- `st'` is `st` with the edges `Es` pushed and counted (output and cursor kept). -/
def EdgeEff (st st' : NSt CR CQ) (Es : List (ℕ × ℕ)) : Prop :=
  st'.stk = Function.update st.stk q4E (pairsRev Es ++ st.stk q4E) ∧
    st'.env r4M = st.env r4M + Es.length ∧ st'.pos = st.pos ∧ st'.out = st.out

lemma EdgeEff.trans {st s₁ s₂ : NSt CR CQ} {E₁ E₂ : List (ℕ × ℕ)} (h₁ : EdgeEff st s₁ E₁)
    (h₂ : EdgeEff s₁ s₂ E₂) : EdgeEff st s₂ (E₁ ++ E₂) := by
  obtain ⟨a1, b1, c1, d1⟩ := h₁
  obtain ⟨a2, b2, c2, d2⟩ := h₂
  refine ⟨?_, ?_, c2.trans c1, d2.trans d1⟩
  · rw [a2, a1, pairsRev_append]; simp
  · rw [b2, b1, List.length_append]; ring

lemma EdgeEff.refl (st : NSt CR CQ) : EdgeEff st st [] := by
  refine ⟨?_, by simp, rfl, rfl⟩
  funext q; by_cases h : q = q4E
  · subst h; simp [pairsRev]
  · simp [Function.update_of_ne h]

lemma EdgeEff.of_frame {st st' : NSt CR CQ} (hs : st'.stk = st.stk) (hm : st'.env r4M = st.env r4M)
    (hp : st'.pos = st.pos) (ho : st'.out = st.out) : EdgeEff st st' [] := by
  have := EdgeEff.refl st
  obtain ⟨a, b, -, -⟩ := this
  exact ⟨by rw [hs, ← a], by rw [hm]; simp, hp, ho⟩

/-! ## One edge -/

/-- Push the edge `(h, v)` and count it. -/
def pE (h v : Ex CR) : CStm CR CQ :=
  .seq (.push q4E h) (.seq (.push q4E v) (.set r4M (.add (rv r4M) (.const 1))))

lemma pE_good {w : ℕ} {x : List Bool} (h v : Ex CR) (st : NSt CR CQ) (hh : h.Fits w st.env)
    (hv : v.Fits w st.env) (hm : st.env r4M + 1 < 2 ^ w) :
    ∃ st', Good x w (pE h v) st st' ((h.size + v.size + 3) * Ex.nodeCost w + 3 * unitCost w) ∧
      EdgeEff st st' [(h.eval st.env, v.eval st.env)] ∧
      ∀ r, r ≠ r4M → st'.env r = st.env r := by
  have r1 := CStm.Good.push (x := x) (q := q4E) hh
  have r2 := CStm.Good.push (x := x) (q := q4E) (st := st.setS q4E (h.eval st.env :: st.stk q4E)) hv
  set s2 := (st.setS q4E (h.eval st.env :: st.stk q4E)).setS q4E
    (v.eval st.env :: (st.setS q4E (h.eval st.env :: st.stk q4E)).stk q4E)
  have r3 := CStm.Good.set (x := x) (w := w) (st := s2) (r := r4M) (e := .add (rv r4M) (.const 1))
    (by simp only [Ex.Fits, rv, Ex.eval, s2, NSt.setS_env]; exact ⟨by omega, by omega, hm⟩)
  refine ⟨_, (r1.seq (r2.seq r3)).mono (by simp only [Ex.size, rv]; nlinarith), ⟨?_, ?_, rfl, rfl⟩,
    fun r hr => by simp [Function.update_of_ne hr, s2]⟩
  · funext q; by_cases hq : q = q4E
    · subst hq; simp [s2, pairsRev]
    · simp [s2, Function.update_of_ne hq]
  · simp [s2, Ex.eval, rv]

/-! ## Optional edges -/

/-- Push `(h, v)` if the flag `f` is set. -/
def pEo (h : Ex CR) (f v : Fin CR) : CStm CR CQ := .ite (rv f) (pE h (rv v)) .skip

lemma pEo_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) (h : Ex CR) (f v : Fin CR) (hf : f ≠ r4M)
    (st : NSt CR CQ) (o : Option ℕ) (ho : st.env f = (if o.isSome then 1 else 0))
    (hv : ∀ a, o = some a → st.env v = a) (hh : h.Fits w st.env) (hvw : st.env v < 2 ^ w)
    (hm : st.env r4M + 1 < 2 ^ w) :
    ∃ st', Good x w (pEo h f v) st st' ((h.size + 10) * Ex.nodeCost w) ∧
      EdgeEff st st' (o.toList.map fun a => (h.eval st.env, a)) ∧
      ∀ r, r ≠ r4M → st'.env r = st.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have h2 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hfF : (rv f : Ex CR).Fits w st.env := by
    simp only [rv, Ex.Fits, ho]; split_ifs <;> omega
  cases o with
  | none =>
    refine ⟨st, (CStm.Good.iteF hfF (by simp [rv, Ex.eval, ho]) CStm.Good.skip).mono ?_,
      EdgeEff.refl st, fun _ _ => rfl⟩
    simp only [condCost, rv, Ex.size]; nlinarith
  | some a =>
    obtain ⟨st', g, eff, fr⟩ := pE_good (x := x) h (rv v) st hh (by simpa [rv, Ex.Fits] using hvw)
      hm
    refine ⟨st', (CStm.Good.iteT hfF (by simp [rv, Ex.eval, ho]) g).mono ?_, ?_, fr⟩
    · simp only [condCost, rv, Ex.size]; nlinarith
    · simpa [rv, Ex.eval, hv a rfl] using eff

/-! ## Coordinate slots -/

/-- The position of a coordinate slot: answer offset `off`, mode `md` (`2`: two labels; else
the bit `ε · seed` of the single label), bit `a`, base `lb`: flag `r4F`, value `r4V`. -/
def cposS (lb off md a : Fin CR) : CStm CR CQ :=
  .ite (.lt (.const 1) (rv md))
    (.seq (.set r4F (.const 1)) (.set r4V (.add (rv lb) (.add (rv off) (rv a)))))
    (.ite (.odd (.add (rv a) (rv md))) (.set r4F (.const 0))
      (.seq (.set r4F (.const 1)) (.set r4V (.add (rv lb) (rv off)))))

/-- The mode of an answer `[s, off, labs, seed]` in `G_ε`. -/
def ansMode (e : ℕ) (a : List ℕ) : ℕ := if a.getD 2 0 = 1 then e * a.getD 3 0 else 2

/-- The optional position computed by `cposS`. -/
def cposN (lb off md a : ℕ) : Option ℕ :=
  if 1 < md then some (lb + (off + a)) else if (a + md) % 2 = 1 then none else some (lb + off)

lemma cposA_eq (LB e : ℕ) (a : List ℕ) (b : ℕ) (hb : b ≤ 1) (he : e ≤ 1) (hs : a.getD 3 0 ≤ 1)
    (hl : a.getD 2 0 = 1 ∨ a.getD 2 0 = 2) :
    cposA LB e a b = cposN LB (a.getD 1 0) (ansMode e a) b := by
  unfold cposA ansMode cposN
  have hes : e * a.getD 3 0 ≤ 1 := by
    calc e * a.getD 3 0 ≤ 1 * 1 := Nat.mul_le_mul he hs
      _ = 1 := rfl
  rcases hl with hl | hl
  · simp only [hl, if_true]
    rw [if_neg (show ¬ 1 < e * a.getD 3 0 by omega)]
    by_cases hb' : b = e * a.getD 3 0
    · rw [if_pos hb', if_neg (show ¬ (b + e * a.getD 3 0) % 2 = 1 by omega)]
    · rw [if_neg hb', if_pos (show (b + e * a.getD 3 0) % 2 = 1 by omega)]
  · simp only [hl, show (2 : ℕ) ≠ 1 by decide, if_false, show (1 : ℕ) < 2 by decide, if_true]
    congr 1; omega

lemma cposS_good {w : ℕ} {x : List Bool} (hw : 2 ≤ w) {lb off md a : Fin CR}
    (d1 : lb ≠ r4F) (d2 : off ≠ r4F) (d3 : md ≠ r4F) (d4 : a ≠ r4F) (d5 : lb ≠ r4V)
    (d6 : off ≠ r4V) (d7 : md ≠ r4V) (d8 : a ≠ r4V)
    (st : NSt CR CQ) (hmd : st.env md ≤ 2) (ha : st.env a ≤ 1)
    (hlt : st.env lb + st.env off + 2 < 2 ^ w) (hV : st.env r4V < 2 ^ w) :
    ∃ st', Good x w (cposS lb off md a) st st' (20 * Ex.nodeCost w) ∧
      st'.env r4F = (if (cposN (st.env lb) (st.env off) (st.env md) (st.env a)).isSome
        then 1 else 0) ∧
      (∀ v, cposN (st.env lb) (st.env off) (st.env md) (st.env a) = some v → st'.env r4V = v) ∧
      st'.env r4V < 2 ^ w ∧ st'.stk = st.stk ∧ st'.pos = st.pos ∧ st'.out = st.out ∧
      ∀ r, r ≠ r4F → r ≠ r4V → st'.env r = st.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have h2 : (4 : ℕ) ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw)
  have hF1 : (Ex.lt (.const 1) (rv md) : Ex CR).Fits w st.env := by
    simp only [Ex.Fits, rv]; omega
  by_cases hc : 1 < st.env md
  · have r1 := CStm.Good.set (x := x) (w := w) (st := st) (r := r4F) (e := .const 1)
      (by simp only [Ex.Fits]; omega)
    set s1 := st.set r4F ((Ex.const 1 : Ex CR).eval st.env)
    have r2 := CStm.Good.set (x := x) (w := w) (st := s1) (r := r4V)
      (e := .add (rv lb) (.add (rv off) (rv a))) (by
        simp only [Ex.Fits, rv, Ex.eval, s1, NSt.set_env, Function.update_of_ne d1,
          Function.update_of_ne d2, Function.update_of_ne d4]
        omega)
    refine ⟨_, (CStm.Good.iteT hF1 (by simp [Ex.eval, rv, hc]) (r1.seq r2)).mono ?_, ?_, ?_, ?_,
      rfl, rfl, rfl, fun r h1 h2 => ?_⟩
    · simp only [condCost, Ex.size, rv]; nlinarith
    · simp [s1, cposN, hc, Ex.eval, Function.update_of_ne (show r4F ≠ r4V by decide)]
    · intro v hv
      simp only [cposN, if_pos hc, Option.some.injEq] at hv
      simp [s1, Ex.eval, rv, Function.update_of_ne d1, Function.update_of_ne d2,
        Function.update_of_ne d4, ← hv]
    · simp [s1, Ex.eval, rv, Function.update_of_ne d1, Function.update_of_ne d2,
        Function.update_of_ne d4]; omega
    · simp [s1, Function.update_of_ne h1, Function.update_of_ne h2]
  · have hF2 : (Ex.odd (.add (rv a) (rv md)) : Ex CR).Fits w st.env := by
      simp only [Ex.Fits, rv, Ex.eval]; omega
    by_cases hodd : (st.env a + st.env md) % 2 = 1
    · have r1 := CStm.Good.set (x := x) (w := w) (st := st) (r := r4F) (e := .const 0)
        (by simp only [Ex.Fits]; omega)
      refine ⟨_, (CStm.Good.iteF hF1 (by simp [Ex.eval, rv, hc])
        (CStm.Good.iteT hF2 (by simp [Ex.eval, rv, hodd]) r1)).mono ?_, ?_, ?_, ?_, rfl, rfl, rfl,
        fun r h1 h2 => ?_⟩
      · simp only [condCost, Ex.size, rv]; nlinarith
      · simp [cposN, hc, hodd, Ex.eval]
      · intro v hv; simp [cposN, hc, hodd] at hv
      · simpa [Function.update_of_ne (show r4V ≠ r4F by decide)] using hV
      · simp [Function.update_of_ne h1]
    · have r1 := CStm.Good.set (x := x) (w := w) (st := st) (r := r4F) (e := .const 1)
        (by simp only [Ex.Fits]; omega)
      set s1 := st.set r4F ((Ex.const 1 : Ex CR).eval st.env)
      have r2 := CStm.Good.set (x := x) (w := w) (st := s1) (r := r4V)
        (e := .add (rv lb) (rv off)) (by
          simp only [Ex.Fits, rv, Ex.eval, s1, NSt.set_env, Function.update_of_ne d1,
            Function.update_of_ne d2]
          omega)
      refine ⟨_, (CStm.Good.iteF hF1 (by simp [Ex.eval, rv, hc])
        (CStm.Good.iteF hF2 (by simp [Ex.eval, rv]; omega) (r1.seq r2))).mono ?_, ?_, ?_, ?_,
        rfl, rfl, rfl, fun r h1 h2 => ?_⟩
      · simp only [condCost, Ex.size, rv]; nlinarith
      · simp [s1, cposN, hc, hodd, Ex.eval, Function.update_of_ne (show r4F ≠ r4V by decide)]
      · intro v hv
        simp only [cposN, if_neg hc, if_neg hodd, Option.some.injEq] at hv
        simp [s1, Ex.eval, rv, Function.update_of_ne d1, Function.update_of_ne d2, ← hv]
      · simp [s1, Ex.eval, rv, Function.update_of_ne d1, Function.update_of_ne d2]; omega
      · simp [s1, Function.update_of_ne h1, Function.update_of_ne h2]

end Lax119563Proofs.Compiler
