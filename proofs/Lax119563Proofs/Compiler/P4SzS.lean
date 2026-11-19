import Lax119563Proofs.Compiler.P4SzLoop

/-!
# Pass `P4` (program): the schema-size scan, assembled

**`p4SzS_good`**: at `schPos I`, with the records `(schRecsUpTo I E).reverse` on `qSch` and
`qT = qSzA = []`, `p4SzS` puts `schAll I ++ qSzB` on `qSzB`, adds `Σ schAll` to `rNt`, keeps
every other stack and ends at `H`.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- **The schema-size scan.** -/
def p4SzS : CStm CR CQ :=
  .seq (moveAllS qSch qT rT rP) (.seq (.set rJ (.const 0)) (.seq p4SLoop (moveAllS qSzA qSzB rT rP)))

lemma p4SLoop_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hk : 1 ≤ k)
    (st : NSt CR CQ) (hrec : ∀ v ∈ schRecsUpTo I I.schemas.length, v < 2 ^ w)
    (hT : st.env rNt + (schAll I).sum + 8 < 2 ^ w) (hI : p4SInv I st st) (hj : st.env rJ = 0) :
    ∃ s', Good (encodeSystem I) w p4SLoop st s'
        (1000 * (H I + (schAll I).sum + 1) * Ex.nodeCost w) ∧ p4SInv I st s' ∧
      s'.env rJ = I.schemas.length := by
  have hU := CStm.nodeCost_ge w
  obtain ⟨s', r, hI', hc'⟩ := Good.loop_var (x := encodeSystem I) (w := w)
    (e := .lt (rv rJ) (rv rE)) (body := p4SBody) (p4SInv I st)
    (fun s => I.schemas.length - s.env rJ) (p4SPot I st) (200 * Ex.nodeCost w)
    (700 * Ex.nodeCost w) (fun s hI => ⟨by
      obtain ⟨hE, -, -, hj, -⟩ := hI
      have := E_le I
      simp only [Ex.Fits, rv, hE]; omega,
      fun hc => p4SBody_good I hw hH hk st s hrec hT hI hc⟩) st hI
  have hJ : s'.env rJ = I.schemas.length := by
    obtain ⟨hE, -, -, hj', -⟩ := hI'
    simp only [Ex.eval, rv, hE] at hc'; split_ifs at hc' with h <;> omega
  refine ⟨s', r.mono ?_, hI', hJ⟩
  have hE := E_le I
  have hpot : p4SPot I st st ≤ H I + (schAll I).sum := by unfold p4SPot; omega
  have hU' := CStm.unitCost_ge w
  have hc : condCost w (Ex.lt (rv rJ) (rv rE) : Ex CR) ≤ 4 * Ex.nodeCost w := by
    simp only [condCost, Ex.size, rv]; omega
  rw [hj, Nat.sub_zero]
  generalize condCost w (Ex.lt (rv rJ) (rv rE) : Ex CR) = c at *
  generalize Ex.nodeCost w = N at *
  generalize p4SPot I st st = φ at *
  generalize H I = h at *
  generalize (schAll I).sum = z at *
  generalize I.schemas.length = E at *
  have h1 : 200 * N * φ ≤ 200 * N * (h + z) := Nat.mul_le_mul_left _ hpot
  have h2 : E * (700 * N + c) ≤ h * (704 * N) := Nat.mul_le_mul hE (by omega)
  nlinarith

lemma p4SzS_arith {N U a b c h z : ℕ} (hU : U ≤ N) (ha : a ≤ c) (hb : b ≤ z) :
    (a + 1) * (10 * N) + (N + U + (1000 * (h + z + 1) * N + (b + 1) * (10 * N))) ≤
      2000 * (h + c + z + 1) * N := by
  nlinarith

/-- **The schema-size scan.** -/
theorem p4SzS_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hk : 1 ≤ k)
    (st : NSt CR CQ) (hb : st.Bdd w) (hpos : st.pos = schPos I)
    (hE : st.env rE = I.schemas.length) (hL1 : st.env rL1 = ℓ + 1) (hK : st.env rKk = k)
    (hSch : st.stk qSch = (schRecsUpTo I I.schemas.length).reverse) (hT0 : st.stk qT = [])
    (hA0 : st.stk qSzA = []) (hT : st.env rNt + (schAll I).sum + 8 < 2 ^ w) :
    ∃ st', Good (encodeSystem I) w p4SzS st st'
        (2000 * (H I + (schRecsUpTo I I.schemas.length).length + (schAll I).sum + 1) *
          Ex.nodeCost w) ∧
      st'.stk = Function.update st.stk qSzB (schAll I ++ st.stk qSzB) ∧
      st'.env rNt = st.env rNt + (schAll I).sum ∧ st'.pos = H I ∧ st'.out = st.out := by
  have hU := CStm.nodeCost_ge w
  have hrec : ∀ v ∈ schRecsUpTo I I.schemas.length, v < 2 ^ w := fun v hv =>
    hb.2 qSch v (by rw [hSch]; exact List.mem_reverse.mpr hv)
  have hp0 : st.pos ≤ (encodeSystem I).length := by
    rw [hpos]; have := schAt_le I 0; rw [schAt_zero] at this; exact this
  obtain ⟨s1, r1, h1s, h1p, h1o, h1e⟩ := moveAllS_good (x := encodeSystem I) hw (q := qSch)
    (q' := qT) (t := rT) (f := rP) (by decide) (by decide) st hb
  have r2 := Good.set (x := encodeSystem I) (w := w) (st := s1) (r := rJ) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  set s2 := s1.set rJ ((Ex.const 0 : Ex CR).eval s1.env)
  have e2 : ∀ r, r ≠ rJ → r ≠ rT → r ≠ rP → s2.env r = st.env r := fun r h1 h2 h3 => by
    simp only [s2, NSt.set_env, Function.update_of_ne h1]; exact h1e r h2 h3
  have e2J : s2.env rJ = 0 := by simp (config := { decide := true }) [s2, Ex.eval]
  have e2s : s2.stk = Function.update (Function.update st.stk qSch []) qT
      (schRecsUpTo I I.schemas.length) := by
    show s1.stk = _; rw [h1s, hSch, hT0, List.reverse_reverse, List.append_nil]
  have hI2 : p4SInv I s2 s2 := by
    refine ⟨by rw [e2 _ (by decide) (by decide) (by decide), hE],
      by rw [e2 _ (by decide) (by decide) (by decide), hL1],
      by rw [e2 _ (by decide) (by decide) (by decide), hK], by rw [e2J]; omega,
      by rw [e2J, schAt_zero]; show s1.pos = _; rw [h1p, hpos],
      by rw [e2J]; simp (config := { decide := true }) [schSzUpTo], ?_, rfl⟩
    rw [e2J, schRecsFrom_zero]
    simp only [schSzUpTo, List.take_zero, List.flatMap_nil, List.reverse_nil, List.nil_append,
      schRecsUpTo, List.take_zero]
    funext q
    by_cases h1 : q = qSzA
    · subst h1; simp
    by_cases h2 : q = qSch
    · subst h2; simp (config := { decide := true }) [e2s, Function.update_of_ne (show qSch ≠ qSzA by decide),
        Function.update_of_ne (show qSch ≠ qT by decide)]
    by_cases h3 : q = qT
    · subst h3; simp (config := { decide := true }) [e2s, Function.update_of_ne (show qT ≠ qSzA by decide),
        Function.update_of_ne (show qT ≠ qSch by decide), schRecsUpTo]
    simp (config := { decide := true }) [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
  have hT2 : s2.env rNt + (schAll I).sum + 8 < 2 ^ w := by
    rw [e2 _ (by decide) (by decide) (by decide)]; exact hT
  obtain ⟨s3, r3, hI3, hJ3⟩ := p4SLoop_good I hw hH hk s2 hrec hT2 hI2 e2J
  obtain ⟨-, -, -, -, h3p, h3n, h3s, h3o⟩ := hI3
  rw [hJ3, schAt_all, schSzUpTo_all, schRecsFrom_all] at *
  have r13 := r1.seq (r2.seq r3)
  have hb3 := r13.bdd hw hb hp0
  obtain ⟨s4, r4, h4s, h4p, h4o, h4e⟩ := moveAllS_good (x := encodeSystem I) hw (q := qSzA)
    (q' := qSzB) (t := rT) (f := rP) (by decide) (by decide) s3 hb3.1
  have e3A : s3.stk qSzA = (schAll I).reverse := by
    rw [h3s]; simp (config := { decide := true }) [e2s, hA0, Function.update_of_ne (show qSzA ≠ qT by decide),
      Function.update_of_ne (show qSzA ≠ qSch by decide)]
  refine ⟨s4, (r1.seq (r2.seq (r3.seq r4))).mono ?_, ?_, ?_, by rw [h4p, h3p], by rw [h4o, h3o]; show s1.out = _; exact h1o⟩
  · rw [e3A, List.length_reverse]
    simp only [Ex.size]
    have := p4SzS_arith (N := Ex.nodeCost w) (U := unitCost w) (a := (st.stk qSch).length)
      (b := (schAll I).length) (c := (schRecsUpTo I I.schemas.length).length) (h := H I)
      (z := (schAll I).sum) hU (by rw [hSch, List.length_reverse])
      (by
        have : ∀ v ∈ schAll I, 1 ≤ v := by
          intro v hv
          simp only [schAll, List.mem_flatMap] at hv
          obtain ⟨e, -, hv⟩ := hv
          rw [schSizes_eq_szL] at hv
          simp only [szL, jlSizes, List.mem_append, List.mem_flatten, List.mem_replicate] at hv
          rcases hv with (((⟨l, ⟨-, rfl⟩, hl⟩ | ⟨-, rfl⟩) | ⟨l, ⟨-, rfl⟩, hl⟩) | ⟨-, rfl⟩) | ⟨-, rfl⟩
          all_goals first | omega | (split_ifs at hl <;> simp at hl <;> omega)
        calc (schAll I).length = ((schAll I).map fun _ => 1).sum := by simp
          _ ≤ (schAll I).sum := by
            have := List.sum_le_sum (l := schAll I) (f := fun _ => 1) (g := id)
              (fun v hv => this v hv)
            simpa using this)
    omega
  · rw [h4s, e3A, List.reverse_reverse, h3s]
    funext q
    by_cases h0 : q = qSzB
    · subst h0; simp (config := { decide := true }) [e2s, Function.update_of_ne (show qSzB ≠ qSzA by decide),
        Function.update_of_ne (show qSzB ≠ qT by decide),
        Function.update_of_ne (show qSzB ≠ qSch by decide)]
    by_cases h1 : q = qSzA
    · subst h1; simp (config := { decide := true }) [hA0]
    by_cases h2 : q = qSch
    · subst h2; simp (config := { decide := true }) [hSch]
    by_cases h3 : q = qT
    · subst h3; simp (config := { decide := true }) [hT0, Function.update_of_ne (show qT ≠ qSzB by decide)]
    simp (config := { decide := true }) [Function.update_of_ne h0, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3, e2s]
  · rw [h4e _ (by decide) (by decide), h3n, e2 _ (by decide) (by decide) (by decide)]

end Lax119563Proofs.Compiler
