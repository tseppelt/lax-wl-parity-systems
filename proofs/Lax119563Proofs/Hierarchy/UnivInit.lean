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

/-! ## The code of a machine -/

/-- The token stream of the code of `M` (without the end token). -/
noncomputable def codeToks (M : Machine) : List Tok :=
  List.replicate (M.tapes + 1) tR ++ tSep :: (List.replicate M.tapes tR ++ tSep :: table M)

/-- The code of `M` as bits. -/
noncomputable def code (M : Machine) : List Bool := (codeToks M ++ [tEnd]).flatMap tokBits

lemma insOf_tokens {M : Machine} (i : Instruction (M.tapes + 1) (M.symbols + 3) (M.states + 1)) :
    ∀ t ∈ insOf M i, 2 ≤ t.val ∧ t.val ≤ 12 := by
  intro t ht
  cases i with
  | halt b => cases b <;> simp [insOf, haltTok] at ht <;> subst ht <;> decide
  | next q w mv =>
    simp only [insOf, insPart, encN, List.mem_cons, List.mem_append, List.mem_replicate,
      List.mem_flatten, List.mem_ofFn, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | (⟨_, rfl⟩ | rfl) | ⟨l, ⟨j, rfl⟩, h⟩
    · decide
    · decide
    · decide
    · simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at h
      rcases h with (⟨_, rfl⟩ | rfl) | rfl
      · decide
      · decide
      · rcases mv j <;> decide

lemma table_tokens (M : Machine) : ∀ t ∈ table M, 2 ≤ t.val ∧ t.val ≤ 12 := by
  intro t ht
  simp only [table, tableToks, entries, List.flatMap_map, List.mem_flatMap] at ht
  obtain ⟨x, -, ht⟩ := ht
  simp only [entryToks, entryOf, List.mem_append, List.mem_cons, List.mem_reverse,
    List.mem_singleton, List.not_mem_nil, or_false] at ht
  rcases ht with (h | rfl | h) | rfl
  · rcases keyToks_tokens _ _ t h with rfl | rfl <;> decide
  · decide
  · exact insOf_tokens _ t h
  · decide

lemma codeToks_tokens (M : Machine) : ∀ t ∈ codeToks M, 2 ≤ t.val ∧ t.val ≤ 13 := by
  intro t ht
  simp only [codeToks, List.mem_append, List.mem_cons, List.mem_replicate] at ht
  rcases ht with ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩ | rfl | h
  · decide
  · decide
  · decide
  · decide
  · have := table_tokens M t h; omega

lemma length_code (M : Machine) : (code M).length = 4 * ((codeToks M).length + 1) := by
  simp only [code, List.length_flatMap, length_tokBits]
  simp [List.sum_replicate, List.map_const']
  ring

/-! ## Initialisation -/

/-- Stacks in the shape used during the initialisation. -/
def ist (aIN aY aP aLS aRS aTBL aFLG : List Tok) : Stacks 16 13 := fun i =>
  if i = IN then aIN else if i = Y then aY else if i = P then aP else if i = LS then aLS else
  if i = RS then aRS else if i = TBL then aTBL else if i = FLG then aFLG else []

lemma records_replicate_nil (n : ℕ) : records (List.replicate n []) = List.replicate n tR := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, records_cons, ih, List.replicate_succ]; simp [record, encL]

lemma encL_symOfBit_le (y : List Bool) : (encL (y.map symOfBit)).length ≤ 3 * y.length := by
  induction y with
  | nil => simp [encL]
  | cons b y ih =>
    simp only [List.map_cons, encL_cons, List.length_append, length_encN, List.length_cons]
    cases b <;> simp [symOfBit] <;> omega

theorem init_runs (M : Machine) (z : List Bool) :
    ∃ s', init.RunsLe (inputStacks 15 13 (code M ++ z)) s'
        (1000 * ((code M ++ z).length + 1)) ∧
      Rel M (Lax489179.TuringMachine.init M (code M ++ z)) s' ∧
      recSize s' ≤ 5 * ((code M ++ z).length + 1) := by
  set y := code M ++ z with hy
  have hct := codeToks_tokens M
  have hlen := length_code M
  have h0 : inputStacks 15 13 y = ist (bitsToks y) [] [] [] [] [] [] := by
    funext i; fin_cases i <;> simp (config := {decide := true}) [inputStacks, ist]
  rw [h0]
  -- parsing
  have h1 := parseLoop_runs (bitsToks z) (codeToks M) (ist (bitsToks y) [] [] [] [] [] []) hct
    (by simp [ist]) (by simp [ist, y, code])
  have h1' := h1.of_eq (s₂ := ist (bitsToks z) (bitsToks (code M)).reverse (codeToks M).reverse [] [] [] [0])
    (by funext i; fin_cases i <;> simp (config := {decide := true}) [update_apply, ist, code])
    le_rfl
  have h2 := (moveAll_runs (i := IN) (j := Y) (by decide) (bitsToks z)
    (ist (bitsToks z) (bitsToks (code M)).reverse (codeToks M).reverse [] [] [] [0]) (by simp [ist])).of_eq
    (s₂ := ist [] (bitsToks y).reverse (codeToks M).reverse [] [] [] [0])
    (by funext i; fin_cases i <;> simp (config := {decide := true}) [update_apply, ist, y]) le_rfl
  have h3 := (RunsLe.pop FLG (ist [] (bitsToks y).reverse (codeToks M).reverse [] [] [] [0])).of_eq
    (s₂ := ist [] (bitsToks y).reverse (codeToks M).reverse [] [] [] [])
    (by funext i; fin_cases i <;> simp (config := {decide := true}) [update_apply, ist]) le_rfl
  have hparse : parse.RunsLe (ist (bitsToks y) [] [] [] [] [] [])
      (ist [] (bitsToks y).reverse (codeToks M).reverse [] [] [] [])
      (200 * ((codeToks M).length + 1) + (19 * z.length + 1 + 1)) := by
    refine (h1'.seq (h2.seq h3)).mono (by simp)
  -- distributing the code
  have h4 : (moveAll P TBL : SProg).RunsLe (ist [] (bitsToks y).reverse (codeToks M).reverse [] [] [] [])
      (ist [] (bitsToks y).reverse [] [] [] (codeToks M) []) (19 * (codeToks M).length + 1) :=
    (moveAll_runs (by decide) (codeToks M).reverse _ (by simp [ist])).of_eq
      (by funext i; fin_cases i <;> simp (config := {decide := true}) [update_apply, ist]) (by simp)
  have hsep : tSep ∉ List.replicate (M.tapes + 1) tR := by simp [List.mem_replicate]
  have hsep' : tSep ∉ List.replicate M.tapes tR := by simp [List.mem_replicate]
  have h5 : (moveWhileNot TBL LS tSep : SProg).RunsLe (ist [] (bitsToks y).reverse [] [] [] (codeToks M) [])
      (ist [] (bitsToks y).reverse [] (List.replicate (M.tapes + 1) tR) []
        (tSep :: (List.replicate M.tapes tR ++ tSep :: table M)) []) (19 * (M.tapes + 1) + 1) :=
    (moveWhileNot_runs (by decide) tSep (tSep :: (List.replicate M.tapes tR ++ tSep :: table M))
      (by simp) (List.replicate (M.tapes + 1) tR) _ hsep (by simp [ist, codeToks])).of_eq
      (by funext i; fin_cases i <;> simp (config := {decide := true}) [update_apply, ist])
      (by simp)
  have h6 : (pop TBL : SProg).RunsLe (ist [] (bitsToks y).reverse [] (List.replicate (M.tapes + 1) tR) []
        (tSep :: (List.replicate M.tapes tR ++ tSep :: table M)) [])
      (ist [] (bitsToks y).reverse [] (List.replicate (M.tapes + 1) tR) []
        (List.replicate M.tapes tR ++ tSep :: table M) []) 1 :=
    (RunsLe.pop _ _).of_eq
      (by funext i; fin_cases i <;> simp (config := {decide := true}) [update_apply, ist]) le_rfl
  have h7 : (moveWhileNot TBL RS tSep : SProg).RunsLe (ist [] (bitsToks y).reverse []
        (List.replicate (M.tapes + 1) tR) [] (List.replicate M.tapes tR ++ tSep :: table M) [])
      (ist [] (bitsToks y).reverse [] (List.replicate (M.tapes + 1) tR) (List.replicate M.tapes tR)
        (tSep :: table M) []) (19 * M.tapes + 1) :=
    (moveWhileNot_runs (by decide) tSep (tSep :: table M) (by simp) (List.replicate M.tapes tR) _ hsep'
      (by simp [ist])).of_eq
      (by funext i; fin_cases i <;> simp (config := {decide := true}) [update_apply, ist])
      (by simp)
  have h8 : (pop TBL : SProg).RunsLe (ist [] (bitsToks y).reverse [] (List.replicate (M.tapes + 1) tR)
        (List.replicate M.tapes tR) (tSep :: table M) [])
      (ist [] (bitsToks y).reverse [] (List.replicate (M.tapes + 1) tR) (List.replicate M.tapes tR)
        (table M) []) 1 :=
    (RunsLe.pop _ _).of_eq
      (by funext i; fin_cases i <;> simp (config := {decide := true}) [update_apply, ist]) le_rfl
  have h9 : (push RS tR : SProg).RunsLe (ist [] (bitsToks y).reverse [] (List.replicate (M.tapes + 1) tR)
        (List.replicate M.tapes tR) (table M) [])
      (ist [] (bitsToks y).reverse [] (List.replicate (M.tapes + 1) tR) (List.replicate (M.tapes + 1) tR)
        (table M) []) 2 :=
    (RunsLe.push _ _ _).of_eq
      (by funext i; fin_cases i <;>
        simp (config := {decide := true}) [update_apply, ist, List.replicate_succ]) le_rfl
  have h10 := inputToRS_runs y.reverse (ist [] (bitsToks y).reverse [] (List.replicate (M.tapes + 1) tR)
    (List.replicate (M.tapes + 1) tR) (table M) []) (by simp [ist, List.map_reverse])
  set sF := ist [] [] [] (List.replicate (M.tapes + 1) tR)
    (encL (y.map symOfBit) ++ List.replicate (M.tapes + 1) tR) (table M) []
  have h10' := h10.of_eq (s₂ := sF)
    (by funext i; fin_cases i <;> simp (config := {decide := true}) [update_apply, ist, sF]) le_rfl
  have hk : M.tapes + 1 ≤ (codeToks M).length := by simp [codeToks]
  have hcy : 4 * ((codeToks M).length + 1) ≤ y.length := by rw [hy, List.length_append, hlen]; omega
  refine ⟨sF, (hparse.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq h10'))))))).mono ?_,
    ⟨rfl, fun _ => [], fun j => if j = 0 then y.map symOfBit else [], fun j => ?_, ?_, ?_, ?_, ?_,
      ?_⟩, ?_⟩
  · simp only [List.length_reverse]
    have : z.length ≤ y.length := by simp [hy]
    omega
  · by_cases hj : j = 0
    · subst hj
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simp only [Lax489179.TuringMachine.init, true_and, if_true, zero_add]
        rw [if_pos (by omega)]
        simp only [Int.toNat_natCast]
        rcases h : y[i]? with _ | _ | _ <;> simp [List.getD_eq_getElem?_getD, h, symOfBit]
      · simp only [Lax489179.TuringMachine.init]
        rw [if_neg (by omega)]
        simp
    · refine ⟨fun i => ?_, fun i => ?_⟩
      · simp [Lax489179.TuringMachine.init, hj]
      · simp [Lax489179.TuringMachine.init, hj]
  · simp only [sF, ist]
    simp (config := {decide := true}) only [if_true, if_false]
    rw [List.ofFn_const, records_replicate_nil]
  · simp only [sF, ist]
    simp (config := {decide := true}) only [if_true, if_false]
    rw [List.ofFn_succ]
    simp only [if_true, Fin.succ_ne_zero, if_false, records_cons, record]
    rw [List.ofFn_const, records_replicate_nil, List.replicate_succ]
    simp
  · simp [sF, ist, Lax489179.TuringMachine.init]
  · simp [sF, ist]
  · intro i h1 h2 h3 h4
    fin_cases i <;> simp_all (config := {decide := true}) [sF, ist]
  · simp only [recSize, sF, ist]
    simp (config := {decide := true}) only [if_true, if_false]
    have := encL_symOfBit_le y
    simp only [List.length_append, List.length_replicate]
    omega

end Lax119563Proofs.Hierarchy.Universal
