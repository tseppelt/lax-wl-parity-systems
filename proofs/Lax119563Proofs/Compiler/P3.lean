import Lax119563Proofs.Compiler.P3Gen
import Lax119563Proofs.Compiler.P3Join

/-!
# Pass `P3` (requests and the join): the assembly

`p3 = p3Gen; p3Join` (**`p3_good`**): from a state with `rW = W`, `rL = ℓ`, `rL1 = ℓ + 1`,
empty generation stacks and `qAns = []`, `p3` leaves the sorted answers on
`qAns` (`ansAll I`, the order of `P4`) within `200000 (H + 1) (log₂ (H + 1) + 1) · nodeCost w`.

The answers are `ansAll I` (`PJoinFacts.p3_answers`): the order in which `P4` consumes them.
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings Lax119563.MatrixCompiler
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-- **Pass `P3`.** -/
def p3 : CStm CR CQ := .seq p3Gen p3Join

lemma p3_arith (N h lg : ℕ) :
    32000 * (h + 1) * N + 150000 * (h + 1) * (lg + 1) * N ≤
      200000 * (h + 1) * (lg + 1) * N := by
  have : 32000 * (h + 1) * N ≤ 32000 * (h + 1) * (lg + 1) * N := by
    have := Nat.le_mul_of_pos_right (32000 * (h + 1)) (Nat.succ_pos lg)
    exact Nat.mul_le_mul_right _ this
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **Pass `P3`.** -/
theorem p3_good {w : ℕ} (hw : 2 ≤ w) (hk : 1 ≤ k) (hE : I.schemas ≠ [])
    (hS : 16 * (H I + 1) ≤ 2 ^ w)
    (st : NSt CR CQ) (hb : st.Bdd w) (hp : st.pos ≤ H I)
    (hW : st.env rW = I.numLocations) (hL : st.env rL = ℓ) (hL1 : st.env rL1 = ℓ + 1)
    (hG : GenEmpty st) (hAns : st.stk qAns = []) (hRecL : (st.stk qRec).length ≤ 6 * (H I + 1)) :
    ∃ st', Good (encodeSystem I) w p3 st st'
        (200000 * (H I + 1) * (Nat.log 2 (H I + 1) + 1) * Ex.nodeCost w) ∧
      st'.stk qAns = (ansAll I).flatten ∧ st'.stk qX = [] ∧ st'.stk qRec = [] ∧
      st'.stk qLs = [] ∧ st'.stk qLs2 = [] ∧ st'.stk qF2 = [] ∧ st'.stk qDl = [] ∧
      st'.stk qDl2 = [] ∧ st'.stk qDom = [] ∧ st'.stk qDom2 = [] ∧ st'.stk qAux = [] ∧
      (∀ q, q ≠ qLs → q ≠ qLs2 → q ≠ qF → q ≠ qF2 → q ≠ qDl → q ≠ qDl2 → q ≠ qDom →
        q ≠ qDom2 → q ≠ qAux → q ≠ qRec → q ≠ qJunk → q ≠ qAns → st'.stk q = st.stk q) ∧
      st'.env rW = I.numLocations ∧ st'.env rL = ℓ ∧ st'.env rL1 = ℓ + 1 ∧ st'.env rKk = k ∧
      st'.env rE = I.schemas.length ∧ st'.env rKL = k * ℓ ∧
      st'.env rCnt = (locRecs I).length ∧ st'.env rSB = (reqs I).length ∧
      st'.pos = H I ∧ st'.out = st.out ∧
      ∀ r, wReg r p3 = false → st'.env r = st.env r := by
  obtain ⟨s1, r1, h1X, h1R, g1, g2, g3, g4, g5, g6, g7, g8, hO1, e1W, e1L, e1L1, e1K, e1E, e1KL,
    e1C, e1SB, h1p, h1o, -, h1e⟩ := p3Gen_good I hw hk hE hS st hb hp hW hL hL1 hG hRecL
  have h1A : s1.stk qAns = [] := by
    rw [hO1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hAns]
  obtain ⟨s2, r2, h2A, h2X, h2S, h2p, h2o, h2e⟩ := p3Join_good I hw hk hE hS s1 h1X g3 g4
    g5 h1A e1L e1C e1SB
  have hall := r1.seq r2
  have hS2 : ∀ q, q ≠ qX → q ≠ qAns → q ≠ qJunk → s2.stk q = s1.stk q := h2S
  refine ⟨s2, hall.mono (p3_arith _ _ _), h2A, h2X, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [h2p, h1p], by rw [h2o, h1o],
    fun r hr => hall.env_of hr⟩
  · rw [hS2 _ (by decide) (by decide) (by decide), h1R]
  · rw [hS2 _ (by decide) (by decide) (by decide), g1]
  · rw [hS2 _ (by decide) (by decide) (by decide), g2]
  · rw [hS2 _ (by decide) (by decide) (by decide), g3]
  · rw [hS2 _ (by decide) (by decide) (by decide), g4]
  · rw [hS2 _ (by decide) (by decide) (by decide), g5]
  · rw [hS2 _ (by decide) (by decide) (by decide), g6]
  · rw [hS2 _ (by decide) (by decide) (by decide), g7]
  · rw [hS2 _ (by decide) (by decide) (by decide), g8]
  · intro q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12
    rw [hS2 q n3 n12 n11, hO1 q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11]
  · rw [h2e _ (by decide), e1W]
  · rw [h2e _ (by decide), e1L]
  · rw [h2e _ (by decide), e1L1]
  · rw [h2e _ (by decide), e1K]
  · rw [h2e _ (by decide), e1E]
  · rw [h2e _ (by decide), e1KL]
  · rw [h2e _ (by decide), e1C]
  · rw [h2e _ (by decide), e1SB]

end Lax119563Proofs.Compiler
