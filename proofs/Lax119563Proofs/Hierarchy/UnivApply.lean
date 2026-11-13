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

end Lax119563Proofs.Hierarchy.Universal
