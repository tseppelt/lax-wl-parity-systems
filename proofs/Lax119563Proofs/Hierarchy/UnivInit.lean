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

lemma length_tokBits (t : Tok) : (tokBits t).length = 4 := rfl

/-- Parsing tokens up to the end token. -/
lemma parseLoop_runs (rest : List Tok) :
    ∀ (ts : List Tok) (s : Stacks 16 13), (∀ t ∈ ts, 2 ≤ t.val ∧ t.val ≤ 13) → s FLG = [] →
      s IN = bitsToks ((ts ++ [tEnd]).flatMap tokBits) ++ rest →
      (loop (isEmpty FLG) (readBits 4 0)).RunsLe s
        (update (update (update (update s IN rest) Y
          ((bitsToks ((ts ++ [tEnd]).flatMap tokBits)).reverse ++ s Y)) P (ts.reverse ++ s P))
          FLG [0]) (200 * (ts.length + 1))
  | [], s, _, hF, hs => by
    have h1 := readBits_runs (tokBits tEnd) 0 s rest (by simpa using hs)
    rw [tokBits_val tEnd (by decide)] at h1
    simp only [emit, tokOf_end] at h1
    have h2 := RunsLe.loopF (c := isEmpty FLG) (p := readBits 4 0)
      (s := update (update (update s IN rest) Y ((bitsToks (tokBits tEnd)).reverse ++ s Y)) FLG
        (0 :: update (update s IN rest) Y ((bitsToks (tokBits tEnd)).reverse ++ s Y) FLG))
      (by simp [tops, isEmpty])
    refine (RunsLe.loopT (by simp [tops, isEmpty, hF]) h1 h2).of_eq ?_ (by simp [length_tokBits])
    funext k; fin_cases k <;> simp (config := {decide := true}) [update_apply, hF]
  | t :: ts, s, hts, hF, hs => by
    have ht := hts t List.mem_cons_self
    have h1 := readBits_runs (tokBits t) 0 s
      (bitsToks ((ts ++ [tEnd]).flatMap tokBits) ++ rest) (by simp [hs])
    rw [tokBits_val t ht.1] at h1
    simp only [emit, tokOf_tok t ht.1 ht.2] at h1
    set s₁ := update (update (update s IN (bitsToks ((ts ++ [tEnd]).flatMap tokBits) ++ rest)) Y
      ((bitsToks (tokBits t)).reverse ++ s Y)) P (t :: s P)
    have h2 := parseLoop_runs rest ts s₁ (fun t h => hts t (List.mem_cons_of_mem _ h))
      (by simp [s₁, hF]) (by simp [s₁])
    refine (RunsLe.loopT (by simp [tops, isEmpty, hF]) h1 h2).of_eq ?_ ?_
    · funext k; fin_cases k <;> simp (config := {decide := true}) [update_apply, s₁]
    · simp [length_tokBits]; omega

/-- The value of an input bit as a symbol of the tape. -/
def symOfBit (b : Bool) : ℕ := if b then 2 else 1

lemma inputToRS_runs :
    ∀ (bs : List Bool) (s : Stacks 16 13), s Y = bitsToks bs →
      inputToRS.RunsLe s (update (update s Y []) RS (encL (bs.reverse.map symOfBit) ++ s RS))
        (10 * bs.length + 1)
  | [], s, hs => (RunsLe.loopF (by simp [tops, nonempty, hs])).of_eq
      (by funext k; fin_cases k <;> simp (config := {decide := true}) [update_apply, hs, encL])
      (by simp)
  | b :: bs, s, hs => by
    set s₁ := update (update s RS (encN (symOfBit b) ++ s RS)) Y (bitsToks bs)
    have hb : (seq (ite (isTop Y tT) (seq (push RS tS) (seq (push RS tU) (push RS tU)))
        (seq (push RS tS) (push RS tU))) (pop Y) : SProg).RunsLe s s₁ 8 := by
      cases b
      · refine ((((RunsLe.push RS tS s).seq (RunsLe.push RS tU _)).iteF
          (by simp [tops, isTop, hs, bitSym])).seq (RunsLe.pop Y _)).of_eq ?_ (by simp)
        funext k; fin_cases k <;>
          simp (config := {decide := true}) [update_apply, s₁, hs, symOfBit, encN]
      · refine ((((RunsLe.push RS tS s).seq ((RunsLe.push RS tU _).seq
          (RunsLe.push RS tU _))).iteT (by simp [tops, isTop, hs, bitSym])).seq
          (RunsLe.pop Y _)).of_eq ?_ (by simp)
        funext k; fin_cases k <;>
          simp (config := {decide := true}) [update_apply, s₁, hs, symOfBit, encN]
    have h2 := inputToRS_runs bs s₁ (by simp [s₁])
    refine (RunsLe.loopT (by simp [tops, nonempty, hs]) hb h2).of_eq ?_ ?_
    · funext k; fin_cases k <;>
        simp (config := {decide := true}) [update_apply, s₁, encL]
    · simp; omega

end Lax119563Proofs.Hierarchy.Universal
