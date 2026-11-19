import Lax119563Proofs.Compiler.P4Loc

/-!
# Pass `P4` (program): the location part of a round

`p4Loc`: `rst`, skip `k, ℓ, W`, `rL1 := rL + 1`, `rNt, r4M, rJ := 0`, the location loop,
skip `E`, `moveAllS qSzA qSzB` (**`p4Loc_good`**: `qSzB := locAll ++ qSzB`,
`rNt = locOff I W = Σ locAll`, cursor at `schPos I`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- The class sizes of all locations. -/
noncomputable def locAll : List ℕ := (List.finRange I.numLocations).flatMap (locSizes I)

lemma locAll_sum : (locAll I).sum = locOff I I.numLocations := by
  rw [locAll, ← locUpTo_all]
  suffices h : ∀ j ≤ I.numLocations, (locUpTo I j).sum = locOff I j from h _ le_rfl
  intro j
  induction j with
  | zero => intro _; simp (config := { decide := true }) [locUpTo, locOff_zero]
  | succ j ih =>
    intro hj
    rw [locUpTo_succ I (by omega), List.sum_append, ih (by omega), locOff_succ I (by omega),
      locSize_eq_mul, locSizes_eq_rep, List.sum_replicate, smul_eq_mul]

/-- **The location part of a round.** -/
def p4Loc : CStm CR CQ :=
  .seq .rst (.seq (skipNumS rT) (.seq (skipNumS rT) (.seq (skipNumS rT)
    (.seq (.set rL1 (.add (rv rL) (.const 1))) (.seq (.set rNt (.const 0))
      (.seq (.set r4M (.const 0)) (.seq (.set rJ (.const 0)) (.seq p4LLoop
        (.seq (skipNumS rT) (moveAllS qSzA qSzB rT rP))))))))))

set_option maxHeartbeats 1000000 in
theorem p4Loc_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hℓ : ℓ ≤ H I)
    (st : NSt CR CQ) (hb : st.Bdd w) (hp : st.pos ≤ H I) (hW : st.env rW = I.numLocations)
    (hL : st.env rL = ℓ) (hA : st.stk qSzA = []) :
    ∃ st', Good (encodeSystem I) w p4Loc st st' (800 * (H I + 1) * Ex.nodeCost w) ∧
      st'.stk = Function.update st.stk qSzB (locAll I ++ st.stk qSzB) ∧
      st'.pos = schPos I ∧ st'.out = st.out ∧ st'.env rNt = locOff I I.numLocations ∧
      st'.env r4M = 0 ∧ st'.env rL1 = ℓ + 1 := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have r0 := Good.rst (x := encodeSystem I) (w := w) (st := st)
  set s0 : NSt CR CQ := { st with pos := 0 }
  have r1 := skipNumS_good (Q := CQ) hw (t := rT) s0 k _ (drop_zero_k I)
  set s1 := skipNumFinal s0 rT k
  have r2 := skipNumS_good (Q := CQ) hw (t := rT) s1 ℓ _
    (by show (encodeSystem I).drop (0 + _) = _; rw [zero_add]; exact drop_ell I)
  set s2 := skipNumFinal s1 rT ℓ
  have r3 := skipNumS_good (Q := CQ) hw (t := rT) s2 I.numLocations _
    (by show (encodeSystem I).drop (0 + (encodeNat k).length + (encodeNat ℓ).length) = _
        rw [zero_add]; exact drop_W I)
  set s3 := skipNumFinal s2 rT I.numLocations
  have e3 : ∀ r, r ≠ rT → s3.env r = st.env r := fun r h => by
    rw [skipNumFinal_env_ne h, skipNumFinal_env_ne h, skipNumFinal_env_ne h]
  have r4 := Good.set (x := encodeSystem I) (w := w) (st := s3) (r := rL1)
    (e := .add (rv rL) (.const 1)) (by
      simp only [Ex.Fits, Ex.eval, rv, e3 _ (show rL ≠ rT by decide), hL]; omega)
  set s4 := s3.set rL1 ((Ex.add (rv rL) (.const 1) : Ex CR).eval s3.env)
  have r5 := Good.set (x := encodeSystem I) (w := w) (st := s4) (r := rNt) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  set s5 := s4.set rNt ((Ex.const 0 : Ex CR).eval s4.env)
  have r6 := Good.set (x := encodeSystem I) (w := w) (st := s5) (r := r4M) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  set s6 := s5.set r4M ((Ex.const 0 : Ex CR).eval s5.env)
  have r7 := Good.set (x := encodeSystem I) (w := w) (st := s6) (r := rJ) (e := .const 0)
    (by simp only [Ex.Fits]; positivity)
  set s7 := s6.set rJ ((Ex.const 0 : Ex CR).eval s6.env)
  have e7 : ∀ r, r ≠ rT → r ≠ rL1 → r ≠ rNt → r ≠ r4M → r ≠ rJ → s7.env r = st.env r :=
    fun r h1 h2 h3 h4 h5 => by
      simp only [s7, s6, s5, s4, NSt.set_env, Function.update_of_ne h2, Function.update_of_ne h3,
        Function.update_of_ne h4, Function.update_of_ne h5]
      exact e3 r h1
  have e7L1 : s7.env rL1 = ℓ + 1 := by
    simp (config := { decide := true }) [s7, s6, s5, s4, Ex.eval, rv, e3 _ (show rL ≠ rT by decide), hL]
  have e7N : s7.env rNt = 0 := by simp (config := { decide := true }) [s7, s6, s5, Ex.eval]
  have e7M : s7.env r4M = 0 := by simp (config := { decide := true }) [s7, s6, Ex.eval]
  have e7J : s7.env rJ = 0 := by simp (config := { decide := true }) [s7, Ex.eval]
  have h7p : s7.pos = posAt I 0 := by
    show 0 + (encodeNat k).length + (encodeNat ℓ).length + (encodeNat I.numLocations).length = _
    rw [posAt_zero]; ring
  have hI7 : p4LInv I s7 s7 := by
    refine ⟨by rw [e7 _ (by decide) (by decide) (by decide) (by decide) (by decide), hW],
      e7L1, by rw [e7J]; omega, by rw [e7J, h7p], by rw [e7J, e7N, locOff_zero], ?_, rfl⟩
    rw [e7J]; simp (config := { decide := true }) [locUpTo]
  obtain ⟨s8, r8, h8p, h8N, h8s, h8o⟩ := p4LLoop_good I hw hH hℓ s7 hI7 e7J
  have r9 := skipNumS_good (Q := CQ) hw (t := rT) s8 I.schemas.length _
    (by rw [h8p]; exact drop_posAt_W I)
  set s9 := skipNumFinal s8 rT I.schemas.length
  have r19 := r0.seq (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq r9))))))))
  have hb9 := r19.bdd hw hb hp
  obtain ⟨s10, r10, h10s, h10p, h10o, h10e⟩ := moveAllS_good (x := encodeSystem I) hw
    (q := qSzA) (q' := qSzB) (t := rT) (f := rP) (by decide) (by decide) s9 hb9.1
  have e9A : s9.stk qSzA = (locAll I).reverse := by
    show s8.stk qSzA = _; rw [h8s]; simp (config := { decide := true }) [s7, s6, s5, s4, s3, s2, s1, s0, hA, locAll]
  have hlenA : (locAll I).length ≤ 2 * H I := by
    have h1 : (locAll I).length ≤ (locAll I).sum := by
      have : ∀ v ∈ locAll I, 1 ≤ v := by
        intro v hv
        simp only [locAll, List.mem_flatMap, locSizes_eq_rep, List.mem_replicate] at hv
        obtain ⟨_, -, -, rfl⟩ := hv; omega
      calc (locAll I).length = ((locAll I).map fun _ => 1).sum := by simp
        _ ≤ (locAll I).sum := by
          have := List.sum_le_sum (l := locAll I) (f := fun _ => 1) (g := id) this
          simpa using this
    rw [locAll_sum] at h1; have := locOff_le_H I I.numLocations; omega
  have hmono : ∀ j ≤ I.numLocations, posAt I 0 ≤ posAt I j := by
    intro j
    induction j with
    | zero => intro _; exact le_rfl
    | succ j ih => intro hj; rw [posAt_succ I (by omega)]; have := ih (by omega); omega
  have hlen3 : (encodeNat k).length + (encodeNat ℓ).length + (encodeNat I.numLocations).length +
      (encodeNat I.schemas.length).length ≤ H I := by
    have h1 := schAt_le I 0
    rw [schAt_zero, schPos] at h1
    have h3 := hmono _ le_rfl
    rw [posAt_zero] at h3
    omega
  refine ⟨s10, (r0.seq (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq
    (r9.seq r10)))))))))).mono ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e9A, List.length_reverse]
    simp only [Ex.size, rv]
    generalize Ex.nodeCost w = N at *
    generalize unitCost w = U at *
    generalize (encodeNat k).length = a at *
    generalize (encodeNat ℓ).length = b at *
    generalize (encodeNat I.numLocations).length = c at *
    generalize (encodeNat I.schemas.length).length = d at *
    generalize (locAll I).length = n at *
    generalize st.pos = p at *
    generalize H I = h at *
    nlinarith
  · rw [h10s, e9A, List.reverse_reverse]
    show Function.update (Function.update s8.stk qSzA []) qSzB (locAll I ++ s8.stk qSzB) = _
    rw [h8s]
    funext q
    by_cases h0 : q = qSzB
    · subst h0; simp (config := { decide := true }) [s7, s6, s5, s4, s3, s2, s1, s0]
    by_cases h1 : q = qSzA
    · subst h1; simp (config := { decide := true }) [hA]
    simp (config := { decide := true }) [Function.update_of_ne h0, Function.update_of_ne h1, s7, s6, s5, s4, s3, s2, s1, s0]
  · rw [h10p]; show s8.pos + _ = _; rw [h8p]; rfl
  · rw [h10o]; show s8.out = _; rw [h8o]; rfl
  · rw [h10e _ (by decide) (by decide)]
    show (skipNumFinal s8 rT _).env rNt = _
    rw [skipNumFinal_env_ne (by decide), h8N]
  · rw [h10e _ (by decide) (by decide)]
    show (skipNumFinal s8 rT _).env r4M = _
    rw [skipNumFinal_env_ne (by decide), r8.env_of (by decide), e7M]
  · rw [h10e _ (by decide) (by decide)]
    show (skipNumFinal s8 rT _).env rL1 = _
    rw [skipNumFinal_env_ne (by decide), r8.env_of (by decide), e7L1]

end Lax119563Proofs.Compiler
