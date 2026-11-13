import Lax119563Proofs.Hierarchy.UnivStep

/-!
# The code of a machine and the initialisation of the simulator

The code of `M` is its token stream `R^{k+1} Sep R^k Sep table End`, each token written with
4 bits.  On an input `code M ++ z` the initialisation of the simulator reaches stacks that
represent the initial configuration of `M` on the whole input.
-/

namespace Lax119563Proofs.Hierarchy.Universal

open Prog Function Lax489179.TuringMachine

/-- Four bits of a token. -/
def tokBits (t : Tok) : List Bool :=
  [decide ((t.val - 2) / 8 % 2 = 1), decide ((t.val - 2) / 4 % 2 = 1),
    decide ((t.val - 2) / 2 % 2 = 1), decide ((t.val - 2) % 2 = 1)]

/-- Accumulating one bit. -/
def bstep (acc : ℕ) (b : Bool) : ℕ := 2 * acc + if b then 1 else 0

lemma tokBits_val : ∀ t : Tok, 2 ≤ t.val → (tokBits t).foldl bstep 0 = t.val - 2 := by decide

lemma tokOf_tok : ∀ t : Tok, 2 ≤ t.val → t.val ≤ 13 → tokOf (t.val - 2) = some t := by decide

lemma tokOf_end : tokOf (tEnd.val - 2) = none := by decide

/-- The effect of emitting the token with code `v`. -/
def emit (v : ℕ) (s : Stacks 16 13) : Stacks 16 13 :=
  match tokOf v with
  | some t => update s P (t :: s P)
  | none => update s FLG (0 :: s FLG)

/-- The bits as input symbols. -/
abbrev bitsToks (bs : List Bool) : List Tok := bs.map (bitSym 13)

lemma readBits_runs :
    ∀ (bs : List Bool) (acc : ℕ) (s : Stacks 16 13) (rest : List Tok),
      s IN = bitsToks bs ++ rest →
      (readBits bs.length acc).RunsLe s
        (emit (bs.foldl bstep acc) (update (update s IN rest) Y ((bitsToks bs).reverse ++ s Y)))
        (30 * bs.length + 2)
  | [], acc, s, rest, hs => by
    simp only [List.map_nil, List.nil_append] at hs
    simp only [List.length_nil, List.foldl_nil, List.map_nil, List.reverse_nil, List.nil_append]
    rcases h : tokOf acc with _ | t
    · simp only [readBits, emit, h]
      refine (RunsLe.push _ _ _).of_eq ?_ (by simp)
      funext k; fin_cases k <;> simp (config := {decide := true}) [update_apply, hs]
    · simp only [readBits, emit, h]
      refine (RunsLe.push _ _ _).of_eq ?_ (by simp)
      funext k; fin_cases k <;> simp (config := {decide := true}) [update_apply, hs]
  | b :: bs, acc, s, rest, hs => by
    have h1 := moveOne_runs (i := IN) (j := Y) (by decide) (a := bitSym 13 b)
      (l := bitsToks bs ++ rest) (s := s) (by simp [hs])
    set s₁ := update (update s IN (bitsToks bs ++ rest)) Y (bitSym 13 b :: s Y)
    have h2 := readBits_runs bs (bstep acc b) s₁ rest (by simp [s₁])
    have he : emit ((b :: bs).foldl bstep acc)
        (update (update s IN rest) Y ((bitsToks (b :: bs)).reverse ++ s Y)) =
        emit (bs.foldl bstep (bstep acc b))
          (update (update s₁ IN rest) Y ((bitsToks bs).reverse ++ s₁ Y)) := by
      congr 1
      funext k; fin_cases k <;> simp (config := {decide := true}) [update_apply, s₁]
    rw [he]
    cases b
    · exact ((h1.seq h2).iteF (by simp [tops, isTop, hs, bitSym])).mono (by simp; omega)
    · exact ((h1.seq h2).iteT (by simp [tops, isTop, hs, bitSym])).mono (by simp; omega)

end Lax119563Proofs.Hierarchy.Universal
