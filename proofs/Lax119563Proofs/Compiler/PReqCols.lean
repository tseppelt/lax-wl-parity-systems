import Lax119563Proofs.Compiler.PReqCol
import Lax119563Proofs.Compiler.PSchLoop

/-!
# Pass `P3`, request generation: the column loop of one argument

`p3Cols` runs `p3Col` over the columns of a domain (listed on `qDom2` as
`(cs.flatMap cdesc)`, blocks nondecreasing), pushing the requests
`colReqs u π cs s₀ t = [reqRec u π c (s₀ + r t) | (c, r) ∈ cs.zipIdx]` (**`p3Cols_good`**).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ}

/-- The requests of the columns `cs` for the argument `(u, π)`. -/
def colReqs (u : ℕ) (π : BlockPerm k ℓ) (cs : List (Coord k ℓ)) (s0 t : ℕ) : List (List ℕ) :=
  cs.zipIdx.map fun q => reqRec u π q.1 (s0 + q.2 * t)

lemma colReqs_take_succ (u : ℕ) (π : BlockPerm k ℓ) (cs : List (Coord k ℓ)) (s0 t : ℕ) {r : ℕ}
    (hr : r < cs.length) :
    colReqs u π (cs.take (r + 1)) s0 t = colReqs u π (cs.take r) s0 t ++
      [reqRec u π cs[r] (s0 + r * t)] := by
  rw [colReqs, colReqs, List.take_add_one, List.getElem?_eq_getElem hr, Option.toList_some,
    List.zipIdx_append, List.map_append]
  simp only [List.length_take, Nat.min_eq_left hr.le, List.zipIdx_cons, List.zipIdx_nil,
    List.map_cons, List.map_nil, zero_add]

/-- The block reached after `r` columns. -/
def curB (cs : List (Coord k ℓ)) (r : ℕ) : ℕ := ((cs.take r).getLast?.map fun c => (c.1 : ℕ)).getD 0

lemma curB_succ (cs : List (Coord k ℓ)) {r : ℕ} (hr : r < cs.length) :
    curB cs (r + 1) = cs[r].1 := by
  rw [curB, List.take_add_one, List.getElem?_eq_getElem hr, Option.toList_some,
    List.getLast?_append]
  simp only [List.getLast?_singleton, Option.some_or, Option.map_some, Option.getD_some]

lemma curB_le (cs : List (Coord k ℓ)) (hs : (cs.map fun c => (c.1 : ℕ)).Pairwise (· ≤ ·))
    {r : ℕ} (hr : r < cs.length) : curB cs r ≤ cs[r].1 := by
  rcases r with _ | r
  · simp [curB]
  · rw [curB_succ cs (by omega)]
    have := List.pairwise_iff_getElem.mp hs r (r + 1) (by simp; omega) (by simp; omega)
      (by omega)
    simpa using this

/-- The column loop. -/
def p3Cols : CStm CR CQ := .seq (.set rK (.const 0)) (.loop (.lt (rv rK) (rv rD)) p3Col)

lemma fL_lt (π : BlockPerm k ℓ) : ∀ v ∈ fL π, v < k := by
  intro v hv; simp only [fL, List.mem_map] at hv; obtain ⟨i, -, rfl⟩ := hv; exact (π.perm i).2

lemma dL_mem (π : BlockPerm k ℓ) : ∀ d ∈ dL π, d.length = ℓ ∧ ∀ v ∈ d, v ≤ 1 := by
  intro d hd; simp only [dL, List.mem_map] at hd; obtain ⟨i, -, rfl⟩ := hd
  exact ⟨length_blockDescription _, blockDescription_le _⟩

lemma cols_arith (N U k n ℓ : ℕ) (hU : U ≤ N) (hU' : 64 ≤ U) :
    1 * N + U + ((ℓ + 3) * (12 * N) * k + n * ((ℓ + 3) * (12 * N) + (ℓ + 2) * (40 * N) +
      ((1 + 1 + 1) * N + 1)) + ((1 + 1 + 1) * N + 1)) ≤ (k + n + 1) * ((ℓ + 3) * (60 * N)) := by
  have h1 : n * ((ℓ + 3) * (12 * N) + (ℓ + 2) * (40 * N) + ((1 + 1 + 1) * N + 1)) ≤
      n * ((ℓ + 3) * (60 * N)) := Nat.mul_le_mul_left _ (by nlinarith)
  have h2 : (ℓ + 3) * (12 * N) * k ≤ k * ((ℓ + 3) * (60 * N)) := by
    rw [mul_comm]; exact Nat.mul_le_mul_left _ (by nlinarith)
  have h3 : 1 * N + U + ((1 + 1 + 1) * N + 1) ≤ (ℓ + 3) * (60 * N) := by nlinarith
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **The column loop of one argument.** -/
lemma p3Cols_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (st : NSt CR CQ) (u : ℕ)
    (π : BlockPerm k ℓ) (cs : List (Coord k ℓ)) (s0 t : ℕ) (R D0 Q0 : List ℕ)
    (hs : (cs.map fun c => (c.1 : ℕ)).Pairwise (· ≤ ·)) (hk : 1 ≤ k)
    (hKw : k + 1 < 2 ^ w) (hℓw : ℓ + 1 < 2 ^ w) (huw : u < 2 ^ w) (hnw : cs.length + 1 < 2 ^ w)
    (hsw : s0 + cs.length * t < 2 ^ w)
    (hD : st.env rD = cs.length) (hX2 : st.stk qDom2 = cs.flatMap cdesc ++ R)
    (hDom : st.stk qDom = D0) (hAux : st.stk qAux = []) (hC : st.env rCur = 0)
    (hL : st.env rL = ℓ) (hU : st.env rU = u) (hS : st.env rSq = s0) (hT : st.env rStr = t)
    (hD2 : st.stk qDl2 = (dL π).flatten) (hF2 : st.stk qF2 = (fL π).drop 1)
    (hFi : st.env rFi = (fL π).getD 0 0) (hRec : st.stk qRec = Q0) :
    ∃ st', Good x w p3Cols st st' ((k + cs.length + 1) * ((ℓ + 3) * (60 * Ex.nodeCost w))) ∧
      st'.stk qDom2 = R ∧ st'.stk qDom = (cs.flatMap cdesc).reverse ++ D0 ∧
      st'.stk qDl2 = ((dL π).drop (curB cs cs.length)).flatten ∧
      st'.stk qF2 = (fL π).drop (curB cs cs.length + 1) ∧ st'.stk qAux = [] ∧
      st'.stk qRec = (colReqs u π cs s0 t).flatten.reverse ++ Q0 ∧
      (∀ q, q ≠ qDom2 → q ≠ qDom → q ≠ qDl2 → q ≠ qF2 → q ≠ qAux → q ≠ qRec → q ≠ qJunk →
        st'.stk q = st.stk q) ∧
      st'.pos = st.pos ∧ st'.out = st.out ∧
      ∀ r, wReg r p3Cols = false → st'.env r = st.env r := by
  have hU0 := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  set n := cs.length
  have r0 := Good.set (x := x) (w := w) (r := rK) (e := .const 0) (st := st)
    (by simp only [Ex.Fits]; omega)
  set s0' := st.set rK ((Ex.const 0 : Ex CR).eval st.env)
  set Inv : NSt CR CQ → Prop := fun s => s.env rK ≤ n ∧ s.env rD = n ∧ s.env rL = ℓ ∧
    s.env rU = u ∧ s.env rStr = t ∧ s.env rSq = s0 + s.env rK * t ∧
    s.env rCur = curB cs (s.env rK) ∧ s.env rFi = (fL π).getD (curB cs (s.env rK)) 0 ∧
    s.stk qDom2 = (cs.drop (s.env rK)).flatMap cdesc ++ R ∧
    s.stk qDom = ((cs.take (s.env rK)).flatMap cdesc).reverse ++ D0 ∧
    s.stk qDl2 = ((dL π).drop (curB cs (s.env rK))).flatten ∧
    s.stk qF2 = (fL π).drop (curB cs (s.env rK) + 1) ∧ s.stk qAux = [] ∧
    s.stk qRec = (colReqs u π (cs.take (s.env rK)) s0 t).flatten.reverse ++ Q0 ∧
    (∀ q, q ≠ qDom2 → q ≠ qDom → q ≠ qDl2 → q ≠ qF2 → q ≠ qAux → q ≠ qRec → q ≠ qJunk →
      s.stk q = st.stk q) ∧
    s.pos = st.pos ∧ s.out = st.out ∧ ∀ r, wReg r p3Cols = false → s.env r = st.env r
    with hInv
  have hloop := Good.loop_var (x := x) (w := w) (e := .lt (rv rK) (rv rD)) (body := p3Col)
    Inv (fun s => n - s.env rK) (fun s => k - s.env rCur) ((ℓ + 3) * (12 * Ex.nodeCost w))
    ((ℓ + 3) * (12 * Ex.nodeCost w) + (ℓ + 2) * (40 * Ex.nodeCost w)) (by
      intro s ⟨hk1, hd, hl, hu, ht, hsq, hcur, hfi, hx2, hdom, hdl, hf2, haux, hrec, hS, hp, ho,
        he⟩
      refine ⟨⟨by simp only [rv, Ex.Fits]; omega, by simp only [rv, Ex.Fits]; omega⟩, ?_⟩
      intro hcond
      have hlt : s.env rK < n := by simpa [rv, Ex.eval, hd] using hcond
      set r := s.env rK with hr
      have hrn : r < cs.length := hlt
      set c := cs[r]
      have hci : curB cs r ≤ (c.1 : ℕ) := curB_le cs hs hrn
      have hik : (c.1 : ℕ) < (fL π).length := by rw [length_fL]; exact c.1.2
      have hx2' : s.stk qDom2 = (c.1 : ℕ) :: blockDescription c.2 ++
          ((cs.drop (r + 1)).flatMap cdesc ++ R) := by
        rw [hx2, List.drop_eq_getElem_cons hrn, List.flatMap_cons]; simp [cdesc, c]
      have hrt : r * t + t ≤ n * t := by
        have : (r + 1) * t ≤ n * t := Nat.mul_le_mul_right _ (by omega)
        rw [add_one_mul] at this; exact this
      obtain ⟨s', r', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
        p3Col_good (x := x) hw s (blockDescription c.2) ((cs.drop (r + 1)).flatMap cdesc ++ R)
          (length_blockDescription _) (blockDescription_le _) (fL π) (dL π)
          (by rw [length_fL, length_dL]) hik hci (dL_mem π)
          (fun v hv => lt_trans (fL_lt π v hv) (by omega)) hℓw (by have := c.1.2; omega) huw
          (by omega) (by omega) hx2' haux hcur hl hu hsq ht hdl hf2 hfi
      have hc1 : curB cs (r + 1) = c.1 := curB_succ cs hrn
      have hK' : s'.env rK = r + 1 := h11
      refine ⟨s', r'.mono ?_, ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩, by rw [hK']; omega, by rw [h8, hcur]; have := hci; omega⟩
      · rw [hcur, h8]
        have : k - curB cs r - (k - c.1) = c.1 - curB cs r := by
          have := c.1.2; omega
        rw [this]; nlinarith
      · rw [h14 _ (by decide), hd]
      · rw [h14 _ (by decide), hl]
      · rw [h14 _ (by decide), hu]
      · rw [h14 _ (by decide), ht]
      · rw [h10, hK']; ring
      · rw [h8, hK', hc1]
      · rw [h9, hK', hc1]
      · rw [h1, hK']
      · rw [h2, hK', hdom, List.take_add_one, List.getElem?_eq_getElem hrn, Option.toList_some,
          List.flatMap_append]
        simp [cdesc, c]
      · rw [h3, hK', hc1]
      · rw [h4, hK', hc1]
      · exact h5
      · rw [h6, hK', colReqs_take_succ _ _ _ _ _ hrn, hrec, reqRec_eq]
        simp [c]
      · intro q n1 n2 n3 n4 n5 n6 n7; rw [h7 q n1 n2 n3 n4 n5 n6 n7, hS q n1 n2 n3 n4 n5 n6 n7]
      · rw [h12, hp]
      · rw [h13, ho]
      · intro q hq
        rw [h14 q (by simp only [p3Cols, wReg, Bool.or_eq_false_iff] at hq; exact hq.2), he q hq])
    s0' ⟨by simp [s0', Ex.eval], by simp [s0', Function.update_of_ne (show rD ≠ rK by decide), hD],
      by simp [s0', Function.update_of_ne (show rL ≠ rK by decide), hL],
      by simp [s0', Function.update_of_ne (show rU ≠ rK by decide), hU],
      by simp [s0', Function.update_of_ne (show rStr ≠ rK by decide), hT],
      by simp [s0', Function.update_of_ne (show rSq ≠ rK by decide), hS, Ex.eval],
      by simp [s0', Function.update_of_ne (show rCur ≠ rK by decide), hC, Ex.eval, curB],
      by simp [s0', Function.update_of_ne (show rFi ≠ rK by decide), hFi, Ex.eval, curB],
      by simp [s0', Ex.eval, hX2], by simp [s0', Ex.eval, hDom], by simp [s0', Ex.eval, hD2, curB],
      by simp [s0', Ex.eval, hF2, curB], by simp [s0', hAux],
      by simp [s0', Ex.eval, hRec, colReqs], fun _ _ _ _ _ _ _ _ => rfl, rfl, rfl,
      fun r hr => by
        simp only [p3Cols, wReg, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
        simp [s0', Function.update_of_ne (Ne.symm hr.1)]⟩
  obtain ⟨s', r', ⟨hk1, hd, -, -, -, -, -, -, hx2, hdom, hdl, hf2, haux, hrec, hS, hp, ho, he⟩,
    hc⟩ := hloop
  have hkn : s'.env rK = n := by
    simp only [Ex.eval, rv, hd] at hc; split_ifs at hc with h <;> omega
  refine ⟨s', (r0.seq r').mono ?_, ?_, ?_, ?_, ?_, haux, ?_, hS, hp, ho, he⟩
  · have h0 : n - s0'.env rK = n := by simp [s0', Ex.eval]
    have h1 : k - s0'.env rCur = k := by
      simp [s0', Function.update_of_ne (show rCur ≠ rK by decide), hC]
    rw [h0, h1]; simp only [condCost, rv, Ex.size]
    exact cols_arith _ _ _ _ _ hU0 hU'
  · rw [hx2, hkn]; simp [n]
  · rw [hdom, hkn, List.take_of_length_le (le_of_eq rfl)]
  · rw [hdl, hkn]
  · rw [hf2, hkn]
  · rw [hrec, hkn, List.take_of_length_le (le_of_eq rfl)]

end Lax119563Proofs.Compiler
