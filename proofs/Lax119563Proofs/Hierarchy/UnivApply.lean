import Lax119563Proofs.Hierarchy.UnivLookup

/-!
# Applying an instruction to the tape records

For each tape, `applyNext` erases the scanned symbol, writes the new one and moves the head
(transferring one symbol between the left and the right part).
-/

namespace Lax119563Proofs.Hierarchy.Universal

open Prog Function Lax489179.TuringMachine

/-- The token of a head move. -/
def mvTok : Move → Tok
  | .left => tL
  | .stay => tZ
  | .right => tRt

/-- The effect of writing `w` and moving by `mv` on a tape given by its left and right parts. -/
def tapeUpd (l r : List ℕ) (w : ℕ) : Move → List ℕ × List ℕ
  | .left => match l with
    | [] => ([], 0 :: w :: r.tail)
    | c :: l' => (l', c :: w :: r.tail)
  | .stay => (l, w :: r.tail)
  | .right => (w :: l, r.tail)

lemma record_cons (c : ℕ) (l : List ℕ) : record (c :: l) = encN c ++ record l := by
  simp [record, encL]

lemma eraseScanned_runs (r : List ℕ) (R : List Tok) (s : Stacks 16 13)
    (hs : s RS = record r ++ R) (hT : s TMP = []) :
    eraseScanned.RunsLe s (update s RS (record r.tail ++ R)) (cK * (r.headD 0 + 2)) := by
  cases r with
  | nil =>
    refine ((RunsLe.skip s).iteT (by simp [tops, isTop, hs, record, encL])).of_eq ?_
      (by simp [cK])
    funext k; by_cases hk : k = RS
    · subst hk; simp [hs]
    · simp [update_of_ne hk]
  | cons c r =>
    have hs' : s RS = List.replicate c tU ++ tS :: (record r ++ R) := by
      rw [hs, record_cons]; simp [encN]
    have h1 := moveThrough_runs (i := RS) (j := TMP) (by decide) (tS_not_mem_rep c) hs'
    have h2 := clear_runs TMP (tS :: ((List.replicate c tU).reverse ++ s TMP))
      (update (update s RS (record r ++ R)) TMP (tS :: ((List.replicate c tU).reverse ++ s TMP)))
      (by simp)
    have hc : isTop RS tR (tops s) = false := by
      cases c <;> simp [tops, hs', isTop, List.replicate_succ]
    refine ((h1.seq h2).iteF hc).of_eq ?_ ?_
    · funext k; fin_cases k <;> simp (config := {decide := true}) [update_apply, hT]
    · simp [hT, cK]; nlinarith

lemma writeSym_runs (w : ℕ) (I : List Tok) (s : Stacks 16 13) (hs : s INS = encN w ++ I)
    (hT : s TMP = []) :
    writeSym.RunsLe s (update (update s INS I) RS (encN w ++ s RS)) (cK * (w + 2)) := by
  have hs' : s INS = List.replicate w tU ++ tS :: I := by rw [hs]; simp [encN]
  have h1 := moveThrough_runs (i := INS) (j := TMP) (by decide) (tS_not_mem_rep w) hs'
  have h2 := moveAll_runs (i := TMP) (j := RS) (by decide)
    (tS :: ((List.replicate w tU).reverse ++ s TMP))
    (update (update s INS I) TMP (tS :: ((List.replicate w tU).reverse ++ s TMP))) (by simp)
  refine (h1.seq h2).of_eq ?_ ?_
  · funext k; fin_cases k <;> simp (config := {decide := true}) [update_apply, hT, encN]
  · simp [hT, cK]; nlinarith

lemma moveHead_runs (l r : List ℕ) (w : ℕ) (mv : Move) (I L R : List Tok) (s : Stacks 16 13)
    (hI : s INS = mvTok mv :: I) (hL : s LS = record l ++ L) (hR : s RS = record (w :: r.tail) ++ R)
    (hT : s TMP = []) :
    moveHead.RunsLe s (update (update (update s INS I) LS (record (tapeUpd l r w mv).1 ++ L)) RS
      (record (tapeUpd l r w mv).2 ++ R)) (cK * (w + l.headD 0 + 3)) := by
  cases mv with
  | left =>
    have hc : isTop INS tL (tops s) = true := by simp [tops, isTop, hI, mvTok]
    have h1 := RunsLe.pop INS s
    set s₁ := update s INS (s INS).tail
    cases l with
    | nil =>
      have hc2 : isTop LS tR (tops s₁) = true := by simp [tops, isTop, s₁, hL, record, encL]
      have h2 := RunsLe.push RS tS s₁
      refine ((h1.seq ((h2.iteT hc2))).iteT hc).of_eq ?_ (by simp [cK]; omega)
      funext k; fin_cases k <;>
        simp (config := {decide := true}) [update_apply, s₁, hI, hL, hR, tapeUpd, record_cons, encN]
    | cons c l =>
      have hL' : s₁ LS = List.replicate c tU ++ tS :: (record l ++ L) := by
        simp [s₁, hL, record_cons, encN]
      have hc2 : isTop LS tR (tops s₁) = false := by
        cases c <;> simp [tops, isTop, s₁, hL, record_cons, encN, List.replicate_succ]
      have h2 := moveThrough_runs (i := LS) (j := TMP) (by decide) (tS_not_mem_rep c) hL'
      set s₂ := update (update s₁ LS (record l ++ L)) TMP
        (tS :: ((List.replicate c tU).reverse ++ s₁ TMP))
      have h3 := moveAll_runs (i := TMP) (j := RS) (by decide)
        (tS :: ((List.replicate c tU).reverse ++ s₁ TMP)) s₂ (by simp [s₂])
      refine ((h1.seq ((h2.seq h3).iteF hc2)).iteT hc).of_eq ?_ ?_
      · funext k; fin_cases k <;>
          simp (config := {decide := true}) [update_apply, s₂, s₁, hI, hL, hR, hT, tapeUpd,
            record_cons, encN]
      · simp [s₁, hT, cK]; nlinarith
  | stay =>
    have hc : isTop INS tL (tops s) = false := by simp [tops, isTop, hI, mvTok]
    have hc2 : isTop INS tRt (tops s) = false := by simp [tops, isTop, hI, mvTok]
    refine (((RunsLe.pop INS s).iteF hc2).iteF hc).of_eq ?_ (by simp [cK]; omega)
    funext k; fin_cases k <;>
      simp (config := {decide := true}) [update_apply, hI, hL, hR, tapeUpd]
  | right =>
    have hc : isTop INS tL (tops s) = false := by simp [tops, isTop, hI, mvTok]
    have hc2 : isTop INS tRt (tops s) = true := by simp [tops, isTop, hI, mvTok]
    have h1 := RunsLe.pop INS s
    set s₁ := update s INS (s INS).tail
    have hR' : s₁ RS = List.replicate w tU ++ tS :: (record r.tail ++ R) := by
      simp [s₁, hR, record_cons, encN]
    have h2 := moveThrough_runs (i := RS) (j := TMP) (by decide) (tS_not_mem_rep w) hR'
    set s₂ := update (update s₁ RS (record r.tail ++ R)) TMP
      (tS :: ((List.replicate w tU).reverse ++ s₁ TMP))
    have h3 := moveAll_runs (i := TMP) (j := LS) (by decide)
      (tS :: ((List.replicate w tU).reverse ++ s₁ TMP)) s₂ (by simp [s₂])
    refine (((h1.seq (h2.seq h3)).iteT hc2).iteF hc).of_eq ?_ ?_
    · funext k; fin_cases k <;>
        simp (config := {decide := true}) [update_apply, s₂, s₁, hI, hL, hR, hT, tapeUpd,
          record_cons, encN]
    · simp [s₁, hT, cK]; nlinarith

@[simp] lemma length_encL_cons (c : ℕ) (l : List ℕ) :
    (encL (c :: l)).length = c + 1 + (encL l).length := by simp [encL]

lemma length_encL_tail (r : List ℕ) :
    (encL r.tail).length + (r.headD 0 + 1) ≤ (encL r).length + 1 := by
  cases r <;> simp <;> omega

lemma tapeUpd_length (l r : List ℕ) (w : ℕ) (mv : Move) :
    (encL (tapeUpd l r w mv).1).length + (encL (tapeUpd l r w mv).2).length ≤
      (encL l).length + (encL r).length + w + 2 := by
  have := length_encL_tail r
  cases mv with
  | left => cases l <;> simp [tapeUpd] <;> omega
  | stay => simp [tapeUpd]; omega
  | right => simp [tapeUpd]; omega

lemma head_le_encL (l : List ℕ) : l.headD 0 ≤ (encL l).length := by
  cases l <;> simp <;> omega

/-- The work on one tape record. -/
def recBody : SProg :=
  seq eraseScanned (seq writeSym (seq moveHead
    (seq (moveThrough LS LS2 tR) (moveThrough RS RS2 tR))))

lemma recBody_runs (l r : List ℕ) (w : ℕ) (mv : Move) (I L R : List Tok) (s : Stacks 16 13)
    (hI : s INS = encN w ++ mvTok mv :: I) (hL : s LS = record l ++ L) (hR : s RS = record r ++ R)
    (hT : s TMP = []) :
    recBody.RunsLe s (update (update (update (update (update s INS I) LS L) RS R) LS2
      ((record (tapeUpd l r w mv).1).reverse ++ s LS2)) RS2
      ((record (tapeUpd l r w mv).2).reverse ++ s RS2))
      (3 * cK * ((encL l).length + (encL r).length + w + 3)) := by
  have h1 := eraseScanned_runs r R s hR hT
  set s₁ := update s RS (record r.tail ++ R)
  have h2 := writeSym_runs w (mvTok mv :: I) s₁ (by simp [s₁, hI]) (by simp [s₁, hT])
  set s₂ := update (update s₁ INS (mvTok mv :: I)) RS (encN w ++ s₁ RS)
  have h3 := moveHead_runs l r w mv I L R s₂ (by simp [s₂]) (by simp [s₂, s₁, hL])
    (by simp [s₂, s₁, record_cons]) (by simp [s₂, s₁, hT])
  set s₃ := update (update (update s₂ INS I) LS (record (tapeUpd l r w mv).1 ++ L)) RS
    (record (tapeUpd l r w mv).2 ++ R)
  have h4 := moveThrough_runs (i := LS) (j := LS2) (by decide) (s := s₃) (l₂ := L)
    (tR_not_mem_encL (tapeUpd l r w mv).1) (by simp [s₃, record])
  set s₄ := update (update s₃ LS L) LS2 (tR :: ((encL (tapeUpd l r w mv).1).reverse ++ s₃ LS2))
  have h5 := moveThrough_runs (i := RS) (j := RS2) (by decide) (s := s₄) (l₂ := R)
    (tR_not_mem_encL (tapeUpd l r w mv).2) (by simp [s₄, s₃, record])
  refine (h1.seq (h2.seq (h3.seq (h4.seq h5)))).of_eq ?_ ?_
  · funext k; fin_cases k <;>
      simp (config := {decide := true}) [update_apply, s₄, s₃, s₂, s₁, hT, record]
  · have e1 := tapeUpd_length l r w mv
    have e2 := head_le_encL l
    have e3 := head_le_encL r
    simp only [cK]
    nlinarith

/-- The tapes as left part, right part, symbol to write and move. -/
abbrev Tp := List ℕ × List ℕ × ℕ × Move

/-- The instruction tokens for the tapes. -/
def insPairs (ts : List Tp) : List Tok := ts.flatMap (fun t => encN t.2.2.1 ++ [mvTok t.2.2.2])

/-- The loop over the tape records in `applyNext`. -/
def recLoop : SProg := loop (nonempty RS) recBody

lemma recLoop_runs :
    ∀ (ts : List Tp) (s : Stacks 16 13), s INS = insPairs ts → s LS = records (ts.map (·.1)) →
      s RS = records (ts.map (·.2.1)) → s TMP = [] →
      recLoop.RunsLe s (update (update (update (update (update s INS []) LS []) RS []) LS2
        ((records (ts.map (fun t => (tapeUpd t.1 t.2.1 t.2.2.1 t.2.2.2).1))).reverse ++ s LS2)) RS2
        ((records (ts.map (fun t => (tapeUpd t.1 t.2.1 t.2.2.1 t.2.2.2).2))).reverse ++ s RS2))
        (3 * cK * ((s LS).length + (s RS).length + (s INS).length + 1) + 1)
  | [], s, hI, hL, hR, _ =>
    (RunsLe.loopF (c := nonempty RS) (p := recBody) (s := s) (by simp [tops, nonempty, hR,
      records])).of_eq (by
        simp only [insPairs, records, List.map_nil, List.flatMap_nil] at hI hL hR
        funext k; fin_cases k <;> simp (config := {decide := true}) [update_apply, hI, hL, hR])
      (by omega)
  | ⟨l, r, w, mv⟩ :: ts, s, hI, hL, hR, hT => by
    have h1 := recBody_runs l r w mv (insPairs ts) (records (ts.map (·.1)))
      (records (ts.map (·.2.1))) s (by simp [hI, insPairs]) (by simp [hL, records_cons])
      (by simp [hR, records_cons]) hT
    set s₁ := update (update (update (update (update s INS (insPairs ts)) LS
      (records (ts.map (·.1)))) RS (records (ts.map (·.2.1)))) LS2
      ((record (tapeUpd l r w mv).1).reverse ++ s LS2)) RS2
      ((record (tapeUpd l r w mv).2).reverse ++ s RS2)
    have h2 := recLoop_runs ts s₁ (by simp [s₁]) (by simp [s₁]) (by simp [s₁]) (by simp [s₁, hT])
    have hc : nonempty RS (tops s) = true := by
      cases r <;> simp [tops, nonempty, hR, records_cons, record, encL, encN] <;>
        cases ‹ℕ› <;> simp
    refine (RunsLe.loopT hc h1 h2).of_eq ?_ ?_
    · funext k; fin_cases k <;>
        simp (config := {decide := true}) [update_apply, s₁, records_cons, List.reverse_append]
    · have eL : (s LS).length = (encL l).length + 1 + (s₁ LS).length := by
        simp [s₁, hL, records_cons]
      have eR : (s RS).length = (encL r).length + 1 + (s₁ RS).length := by
        simp [s₁, hR, records_cons]
      have eI : (s INS).length = w + 2 + (s₁ INS).length := by
        simp [s₁, hI, insPairs]; omega
      rw [eL, eR, eI]
      simp only [cK]
      omega

end Lax119563Proofs.Hierarchy.Universal
