import Lax119563Proofs.Compiler.P4LocPass
import Lax119563Proofs.Compiler.P4SchLab

/-!
# Pass `P4`, schema part: skipping the location section

`p4KLoop` skips the descriptions of all locations (per location: `ι`, `|D|`, the coordinates)
(**`p4KLoop_good`**: from `posAt I 0` with `rJ = 0` to `posAt I W`, writing only
`rT, rP, r4D, rc2, rc3, rJ`).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- Skip the description of one location. -/
def p4KBody : CStm CR CQ :=
  .seq (skipNumS rT) (.seq (rdNumS r4D rP rT) (.seq (skipBlocksS r4D rL1 rc2 rc3 rT)
    (.set rJ (.add (rv rJ) (.const 1)))))

/-- Skip the location section. -/
def p4KLoop : CStm CR CQ := .loop (.lt (rv rJ) (rv rW)) p4KBody

/-- Registers written by `p4KLoop`. -/
def kW : List (Fin CR) := [rT, rP, r4D, rc2, rc3, rJ]

/-- The loop invariant. -/
def p4KInv (st s : NSt CR CQ) : Prop :=
  s.env rW = I.numLocations ∧ s.env rL1 = ℓ + 1 ∧
    s.env rJ ≤ I.numLocations ∧ s.pos = posAt I (s.env rJ) ∧ s.stk = st.stk ∧
    s.out = st.out ∧ ∀ r, r ∉ kW → s.env r = st.env r

lemma p4KBody_arith {N U la ld lf d : ℕ} (hU : U ≤ N) (hU' : 64 ≤ U) (hdf : N * d ≤ N * lf) :
    (la + 1) * (4 * N) + ((ld + 1) * (20 * N) + ((lf + d + 1) * (50 * N) +
      ((1 + 1 + 1) * N + U))) ≤ 150 * N * (la + ld + lf) + 200 * N := by
  nlinarith

lemma p4KBody_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hℓ : ℓ ≤ H I)
    (st s : NSt CR CQ) (hI : p4KInv I st s) (hc : (Ex.lt (rv rJ) (rv rW)).eval s.env ≠ 0) :
    ∃ s', Good (encodeSystem I) w p4KBody s s'
        (150 * Ex.nodeCost w * ((H I - s.pos) - (H I - s'.pos)) + 200 * Ex.nodeCost w) ∧
      p4KInv I st s' ∧ I.numLocations - s'.env rJ < I.numLocations - s.env rJ ∧
      H I - s'.pos ≤ H I - s.pos := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  have hH2 : 2 * (H I + 1) ≤ 2 ^ w := by omega
  obtain ⟨hW, hL1, hjW, hpos, hstk, hout, hfr⟩ := hI
  have hlt : s.env rJ < I.numLocations := by
    by_contra h; apply hc; simp only [Ex.eval, rv, hW]; rw [if_neg h]
  set j := s.env rJ with hjdef
  set v : Fin I.numLocations := ⟨j, hlt⟩
  set a := initNum (I.init v)
  set d := (coordList (I.domain v)).length
  set bs := (locNums I v).map (coordNumDescription ℓ)
  have hbsl : bs.length = d := by simp [bs, length_locNums, d]
  have hbsM : ∀ b ∈ bs, b.length = ℓ + 1 := by
    intro b hb
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hb
    simp [coordNumDescription]
  have hfl : bs.flatten.length = d * (ℓ + 1) := length_flatten_cnd I v
  set rest := encodeNats (locsSuf I (j + 1) ++ I.schemas.length :: schsDesc I)
  have hx : (encodeSystem I).drop s.pos =
      encodeNat a ++ (encodeNat d ++ (encodeNats bs.flatten ++ rest)) := by
    rw [hpos, drop_posAt, locsSuf_cons I hlt, locD_eq', List.append_assoc, List.cons_append,
      List.cons_append, encNats_cons, encNats_cons, encodeNats_append]
  have hposle : s.pos ≤ H I := by rw [hpos]; exact posAt_le I j
  have hlenx : s.pos + (encodeNat a).length + (encodeNat d).length +
      (encodeNats bs.flatten).length ≤ H I := by
    have := congrArg List.length hx
    simp only [List.length_drop, List.length_append] at this
    have : s.pos ≤ (encodeSystem I).length := hposle
    show _ ≤ (encodeSystem I).length
    omega
  have hdf : d ≤ (encodeNats bs.flatten).length :=
    le_trans (by rw [hfl]; nlinarith) (length_le_encodeNats _)
  have hdH : d ≤ H I := by omega
  have hd : (Nat.bits d).length < w := bits_lt_of_le hdH hH2
  -- skipping `ι(v)`, reading `|D_v|`
  have r1 := skipNumS_good (Q := CQ) hw (t := rT) s a _ hx
  set s1 := skipNumFinal s rT a
  have hx2 : (encodeSystem I).drop s1.pos = encodeNat d ++ (encodeNats bs.flatten ++ rest) := by
    simp only [s1, skipNumFinal]
    rw [← List.drop_drop, hx, List.drop_left]
  have r2 := rdNumS_good (Q := CQ) hw (r := r4D) (p := rP) (t := rT) (by decide) (by decide)
    (by decide) s1 d _ hx2 hd
  set s2 := rdNumFinal s1 r4D rP rT d
  have e2 : ∀ q, q ≠ r4D → q ≠ rP → q ≠ rT → s2.env q = s.env q := by
    intro q h1 h3 h4
    rw [rdNumFinal_env_ne h1 h3 h4, skipNumFinal_env_ne h4]
  have e2D : s2.env r4D = d := rdNumFinal_env_r (by decide) (by decide) d
  -- skipping the coordinates
  have hx4 : (encodeSystem I).drop s2.pos = encodeNats bs.flatten ++ rest := by
    simp only [s2, rdNumFinal_pos]
    rw [← List.drop_drop, hx2, List.drop_left]
  obtain ⟨s5, r5, hs5, hp5, ho5, hf5⟩ := skipBlocksS_good (Q := CQ) hw (d := r4D) (m := rL1)
    (j := rc2) (i := rc3) (t := rT) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) s2 bs (ℓ + 1) hbsM rest hx4
    (by rw [hbsl, e2D])
    (by rw [e2 rL1 (by decide) (by decide) (by decide), hL1])
    (by rw [hbsl]; omega) (by omega)
  have e5J : s5.env rJ = j := by
    rw [hf5 _ (by decide) (by decide) (by decide), e2 _ (by decide) (by decide) (by decide)]
  have r6 := Good.set (x := encodeSystem I) (w := w) (r := rJ) (e := .add (rv rJ) (.const 1))
    (st := s5) (by
      have := W_le I
      simp only [Ex.Fits, Ex.eval, rv, e5J]; omega)
  set s6 := s5.set rJ (Ex.eval s5.env (.add (rv rJ) (.const 1)))
  have e6 : ∀ q, q ≠ rJ → s6.env q = s5.env q := fun q hq => by
    simp [s6, Function.update_of_ne hq]
  have e6J : s6.env rJ = j + 1 := by simp [s6, Ex.eval, rv, e5J]
  have back : ∀ q, q ∉ kW → s6.env q = s.env q := by
    intro q hq
    simp only [kW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hq
    rw [e6 q h6, hf5 q h4 h5 h1, e2 q h3 h2 h1]
  have hp6 : s6.pos = s.pos + (encodeNat a).length + (encodeNat d).length +
      (encodeNats bs.flatten).length := by
    rw [NSt.set_pos, hp5]; rfl
  refine ⟨s6, (r1.seq (r2.seq (r5.seq r6))).mono ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hp6]
    have hΔ : H I - s.pos - (H I - (s.pos + (encodeNat a).length + (encodeNat d).length +
        (encodeNats bs.flatten).length)) = (encodeNat a).length + (encodeNat d).length +
        (encodeNats bs.flatten).length := by omega
    rw [hΔ, hbsl]
    simp only [Ex.size, rv]
    generalize Ex.nodeCost w = N at *
    generalize unitCost w = U at *
    generalize (encodeNat a).length = la at *
    generalize (encodeNat d).length = ld at *
    generalize (encodeNats bs.flatten).length = lf at *
    exact p4KBody_arith hU hU' (Nat.mul_le_mul_left N hdf)
  · rw [back _ (by decide), hW]
  · rw [back _ (by decide), hL1]
  · rw [e6J]; omega
  · rw [e6J, hp6, hpos, posAt_succ I hlt, locD_eq']
    simp only [encNats_cons, List.length_append]; ring
  · rw [NSt.set_stk, hs5]; exact hstk
  · rw [NSt.set_out, ho5]; exact hout
  · intro r hr; rw [back r hr, hfr r hr]
  · rw [e6J]; omega
  · rw [hp6]; omega

/-- **Skipping the location section.** -/
lemma p4KLoop_good {w : ℕ} (hw : 2 ≤ w) (hH : 4 * (H I + 1) ≤ 2 ^ w) (hℓ : ℓ ≤ H I)
    (st : NSt CR CQ) (hI : p4KInv I st st) (hj : st.env rJ = 0) :
    ∃ st', Good (encodeSystem I) w p4KLoop st st' (400 * (H I + 1) * Ex.nodeCost w) ∧
      st'.pos = posAt I I.numLocations ∧ st'.stk = st.stk ∧ st'.out = st.out ∧
      ∀ r, r ∉ kW → st'.env r = st.env r := by
  have hU := CStm.nodeCost_ge w
  have hU' := CStm.unitCost_ge w
  obtain ⟨s7, r7, hI7, hc7⟩ := Good.loop_var (x := encodeSystem I) (w := w)
    (e := .lt (rv rJ) (rv rW)) (body := p4KBody) (p4KInv I st)
    (fun s => I.numLocations - s.env rJ) (fun s => H I - s.pos) (150 * Ex.nodeCost w)
    (200 * Ex.nodeCost w) (fun s hI => ⟨by
      obtain ⟨hW, -, hj, -⟩ := hI
      have := W_le I
      simp only [Ex.Fits, rv, hW]; omega, fun hc => p4KBody_good I hw hH hℓ st s hI hc⟩) st hI
  obtain ⟨hW7, -, hj7, hpos7, hstk7, hout7, hfr7⟩ := hI7
  have hjW : s7.env rJ = I.numLocations := by
    simp only [Ex.eval, rv, hW7] at hc7; split_ifs at hc7 with h <;> omega
  refine ⟨s7, r7.mono ?_, by rw [hpos7, hjW], hstk7, hout7, hfr7⟩
  have hW := W_le I
  have hc : condCost w (Ex.lt (rv rJ) (rv rW) : Ex CR) ≤ 4 * Ex.nodeCost w := by
    simp only [condCost, Ex.size, rv]; omega
  rw [hj, Nat.sub_zero]
  have hφ : H I - st.pos ≤ H I := Nat.sub_le _ _
  generalize condCost w (Ex.lt (rv rJ) (rv rW) : Ex CR) = c at *
  generalize Ex.nodeCost w = N at *
  generalize H I - st.pos = φ at *
  generalize H I = h at *
  generalize I.numLocations = W at *
  have h1 : 150 * N * φ ≤ 150 * N * h := Nat.mul_le_mul_left _ hφ
  have h2 : W * (200 * N + c) ≤ h * (204 * N) := Nat.mul_le_mul hW (by omega)
  nlinarith

end Lax119563Proofs.Compiler
