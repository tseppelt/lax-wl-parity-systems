import Lax119563Proofs.Compiler.PReqLoopList

/-!
# Pass `P3`, request generation: the loop over the schemas

`p3Loop` runs `p3Sch` for `rJ = j, …, E - 1`; started at `schAt I 0` with `rJ = 0`,
`rSB = 0` and empty generation stacks, it pushes `(reqs I).flatten.reverse` onto `qRec`
and ends at the end of the input with `rSB = ansBase I E = |reqs I|` (**`p3Loop_good`**).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- **The schema loop of the request generation.** -/
def p3Loop : CStm CR CQ := .loop (.lt (rv rJ) (rv rE)) p3Sch

/-- The generation stacks. -/
def GenEmpty (s : NSt CR CQ) : Prop :=
  s.stk qLs = [] ∧ s.stk qLs2 = [] ∧ s.stk qF = [] ∧ s.stk qF2 = [] ∧ s.stk qDl = [] ∧
    s.stk qDl2 = [] ∧ s.stk qDom = [] ∧ s.stk qDom2 = [] ∧ s.stk qAux = []

/-- The stacks other than the generation stacks, `qRec` and `qJunk`. -/
def OtherStk (st s : NSt CR CQ) : Prop :=
  ∀ q, q ≠ qLs → q ≠ qLs2 → q ≠ qF → q ≠ qF2 → q ≠ qDl → q ≠ qDl2 → q ≠ qDom →
    q ≠ qDom2 → q ≠ qAux → q ≠ qRec → q ≠ qJunk → s.stk q = st.stk q

/-- The invariant of the schema loop. -/
def p3Inv (w : ℕ) (st s : NSt CR CQ) : Prop :=
  s.env rJ ≤ I.schemas.length ∧ s.env rE = I.schemas.length ∧ s.env rKk = k ∧
    s.env rKL = k * ℓ ∧ s.env rL = ℓ ∧ s.env rL1 = ℓ + 1 ∧ s.env rSB = ansBase I (s.env rJ) ∧
    s.pos = schAt I (s.env rJ) ∧ GenEmpty s ∧
    s.stk qRec = (reqsUpTo I (s.env rJ)).flatten.reverse ++ st.stk qRec ∧ OtherStk st s ∧
    s.out = st.out ∧ s.Bdd w

set_option maxHeartbeats 4000000 in
/-- One schema of the loop. -/
lemma p3Loop_step {w : ℕ} (hw : 2 ≤ w) (hk : 1 ≤ k) (hE : I.schemas ≠ [])
    (hS : 16 * (H I + 1) ≤ 2 ^ w) (st s : NSt CR CQ) (hI : p3Inv I w st s)
    (hc : (Ex.lt (rv rJ) (rv rE)).eval s.env ≠ 0) :
    ∃ s', Good (encodeSystem I) w p3Sch s s'
        (10000 * Ex.nodeCost w * ((H I - s.pos) - (H I - s'.pos)) + 10000 * Ex.nodeCost w) ∧
      p3Inv I w st s' ∧ I.schemas.length - s'.env rJ < I.schemas.length - s.env rJ ∧
      H I - s'.pos ≤ H I - s.pos := by
  obtain ⟨hJ, hEr, hKk, hKL, hL, hL1, hSB, hpos, ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩, hRec,
    hOth, hout, hb⟩ := hI
  have hlt : s.env rJ < I.schemas.length := by
    by_contra h; apply hc; simp only [Ex.eval, rv, hEr]; rw [if_neg h]
  obtain ⟨j, hjdef⟩ : ∃ j, s.env rJ = j := ⟨_, rfl⟩
  rw [hjdef] at hlt hSB hpos hRec
  set e : Fin I.schemas.length := ⟨j, hlt⟩
  have hkH := k_le_H I hE
  have hℓ := ell_le_H I hk (fun h => hE h.2)
  have hEH := E_le I
  have hPLH := kl_le_H I hE
  have h3H := three_le_H I
  have hx : (encodeSystem I).drop s.pos =
      encodeNats (schemaDescription (sch I e)) ++ encodeNats (schsSuf I (j + 1)) := by
    rw [hpos, drop_schAt, schsSuf_cons I hlt, encodeNats_append]; rfl
  have hsch : schAt I (j + 1) = schAt I j + (encodeNats (schD I e)).length := schAt_succ I hlt
  have hschle := schAt_le I (j + 1)
  have hd1 := dom_mul_le I e
  have hdl : (coordList (dom I e)).length ≤ (coordList (dom I e)).length * (ℓ + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hab := ansBase_mul_le I j
  have hab' : ansBase I j ≤ ansBase I j * (ℓ + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hpre : (encodeNats (schsPre I j)).length + (encodeNats (schD I e)).length ≤ H I := by
    have := schsPre_enc_le I (j + 1)
    rw [schsPre_succ I hlt, encodeNats_append, List.length_append] at this
    exact this
  have hpx : s.pos ≤ (encodeSystem I).length := by rw [hpos]; exact schAt_le I j
  obtain ⟨s', r, h1, h2, h3, h4, h5, h6, h7, h8, h9, hRec', hOth', hSB', hJ', hp', ho', he'⟩ :=
    p3Sch_good (x := encodeSystem I) hw s hb hpx (sch I e) (ansBase I j) j (3 * (H I + 1))
      _ hk hx (by omega) (fun v hv => (schD_vals_le I hkH e v hv).trans (by omega))
      (by have := schD_le_H I e; exact hd1.trans (this.trans (by omega)))
      (by nlinarith)
      (by
        show ansBase I j + 3 * (coordList (dom I e)).length + 3 ≤ _
        have : (encodeNats (schD I e)).length ≤ H I := schD_le_H I e
        omega)
      (by omega) (by omega) hKk hKL hL hL1 hSB hjdef g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hlen : s'.pos = schAt I (j + 1) := by rw [hp', hsch, hpos]; rfl
  refine ⟨s', r.mono ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩,
    ?_, ?_, ?_, (r.bdd hw hb hpx).1⟩, ?_, ?_⟩
  · rw [hlen, hsch, hpos]
    have : H I - schAt I j - (H I - (schAt I j + (encodeNats (schD I e)).length)) =
        (encodeNats (schD I e)).length := by omega
    rw [this]; show _ ≤ _ + _
    rw [schD]; nlinarith
  · rw [hJ']; omega
  · rw [he' _ (by decide), hEr]
  · rw [he' _ (by decide), hKk]
  · rw [he' _ (by decide), hKL]
  · rw [he' _ (by decide), hL]
  · rw [he' _ (by decide), hL1]
  · rw [hSB', hJ', ansBase_succ I hlt]; rfl
  · rw [hJ', hlen]
  · rw [hRec', hRec, hJ', reqsUpTo_succ I hlt, argsReqs_eq_reqsE]
    simp; rfl
  · intro q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11
    rw [hOth' q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11, hOth q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11]
  · rw [ho', hout]
  · rw [hJ']; omega
  · rw [hlen, hpos]; omega

lemma p3Loop_arith (N U h E φ : ℕ) (hU : 1 ≤ N) (hφ : φ ≤ h) (hE : E ≤ h) :
    10000 * N * φ + E * (10000 * N + ((1 + 1 + 1) * N + 1)) + ((1 + 1 + 1) * N + 1) ≤
      30000 * (h + 1) * N + U := by
  have e1 : 10000 * N * φ ≤ 10000 * N * h := Nat.mul_le_mul_left _ hφ
  have e2 : E * (10000 * N + ((1 + 1 + 1) * N + 1)) ≤ h * (10000 * N + ((1 + 1 + 1) * N + 1)) :=
    Nat.mul_le_mul_right _ hE
  have e3 : h ≤ h * N := Nat.le_mul_of_pos_right _ hU
  have e4 : 10000 * N * h + h * (10000 * N + ((1 + 1 + 1) * N + 1)) = 20003 * (h * N) + h := by
    ring
  have e5 : 30000 * (h + 1) * N = 30000 * (h * N) + 30000 * N := by ring
  omega

set_option maxHeartbeats 2000000 in
/-- **The schema loop.** -/
theorem p3Loop_good {w : ℕ} (hw : 2 ≤ w) (hk : 1 ≤ k) (hE : I.schemas ≠ [])
    (hS : 16 * (H I + 1) ≤ 2 ^ w) (st : NSt CR CQ) (hb : st.Bdd w) (hJ : st.env rJ = 0)
    (hEr : st.env rE = I.schemas.length) (hKk : st.env rKk = k) (hKL : st.env rKL = k * ℓ)
    (hL : st.env rL = ℓ) (hL1 : st.env rL1 = ℓ + 1) (hSB : st.env rSB = 0)
    (hpos : st.pos = schPos I) (hG : GenEmpty st) :
    ∃ st', Good (encodeSystem I) w p3Loop st st' (30000 * (H I + 1) * Ex.nodeCost w) ∧
      GenEmpty st' ∧ st'.stk qRec = (reqs I).flatten.reverse ++ st.stk qRec ∧ OtherStk st st' ∧
      st'.env rSB = (reqs I).length ∧ st'.pos = H I ∧ st'.out = st.out ∧ st'.Bdd w ∧
      ∀ r, wReg r p3Sch = false → st'.env r = st.env r := by
  have hU := CStm.nodeCost_ge w
  have hI0 : p3Inv I w st st := by
    refine ⟨by rw [hJ]; omega, hEr, hKk, hKL, hL, hL1, by rw [hSB, hJ]; simp [ansBase],
      by rw [hpos, hJ, schAt_zero], hG, by rw [hJ]; simp [reqsUpTo], fun _ _ _ _ _ _ _ _ _ _ _ _ =>
      rfl, rfl, hb⟩
  obtain ⟨s', r, hI', hc'⟩ := Good.loop_var (x := encodeSystem I) (w := w)
    (e := .lt (rv rJ) (rv rE)) (body := p3Sch) (p3Inv I w st)
    (fun s => I.schemas.length - s.env rJ) (fun s => H I - s.pos) (10000 * Ex.nodeCost w)
    (10000 * Ex.nodeCost w) (fun s hI => ⟨by
      obtain ⟨hj, hE', -⟩ := hI
      simp only [Ex.Fits, rv, hE']
      have := E_le I
      have h2 : 2 * (H I + 1) ≤ 2 ^ w := by omega
      omega,
      fun hc => p3Loop_step I hw hk hE hS st s hI hc⟩) st hI0
  obtain ⟨hJ7, hE7, -, -, -, -, hSB7, hp7, hG7, hRec7, hOth7, ho7, hb7⟩ := hI'
  have hj : s'.env rJ = I.schemas.length := by
    simp only [Ex.eval, rv, hE7] at hc'; split_ifs at hc' with h <;> omega
  refine ⟨s', r.mono ?_, hG7, by rw [hRec7, hj, reqsUpTo_all], hOth7,
    by rw [hSB7, hj, ← length_reqsUpTo, reqsUpTo_all], by rw [hp7, hj, schAt_all], ho7, hb7,
    fun q hq => r.env_of (by simpa [wReg] using hq)⟩
  have hU0 := Ex.unitCost_le_nodeCost w
  have hU' := CStm.unitCost_ge w
  simp only [condCost, Ex.size, rv]
  have := p3Loop_arith (Ex.nodeCost w) 0 (H I) (I.schemas.length - st.env rJ) (H I - st.pos)
    (by omega) (by omega) (by have := E_le I; omega)
  omega

end Lax119563Proofs.Compiler
