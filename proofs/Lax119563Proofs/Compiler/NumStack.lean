import Lax119563Proofs.Reduction.HRoutines

/-!
# Number stacks

A *number stack* holds a list of numbers `vs` (top number first) as the symbols
`bs (encodeNats vs)`: the same format as the input stack, so the top number reads like the
next number of an input. Routines on the stack machine (`Hierarchy.Prog K 0`):

* `nsPush r q t`: push the value `v` of the binary register `r` (`nst v`) onto `q`
  (`nsPush_runs`, cost `O(|bits v|)`, helper `t` empty before and after, `r` unchanged);
* `nsPop q r t`: pop the top number of `q` into `r` (`nsPop_runs`).
-/

open Function Lax119563.BinaryEncodings

namespace Lax119563Proofs.Compiler

open Hierarchy Hierarchy.Prog Lax119563Proofs.Reduction

variable {K : ℕ}

/-- The symbols of a pair code `1 d` per digit. -/
def pairs (l : List Bool) : List Bool := l.flatMap fun d => [true, d]

@[simp] lemma pairs_nil : pairs [] = [] := rfl
@[simp] lemma pairs_cons (d : Bool) (l : List Bool) : pairs (d :: l) = true :: d :: pairs l := rfl
lemma pairs_append (l l' : List Bool) : pairs (l ++ l') = pairs l ++ pairs l' := by
  simp [pairs]
@[simp] lemma length_pairs (l : List Bool) : (pairs l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons d l ih => simp [ih]; ring

lemma encodeNat_eq_pairs (v : ℕ) : encodeNat v = pairs (Nat.bits v) ++ [false] := rfl

/-! ## Push -/

/-- Pop the bits of `t` (most significant on top), pushing each back onto `r` and its code
`1 d` onto `q`. -/
def pushLoop (t r q : Fin K) : Prog K 0 :=
  loop (fun u => (u t).isSome)
    (bit1 t fun d => seq (pop t) (seq (push r (sym d)) (seq (push q (sym d)) (push q 1))))

lemma pushLoop_runs {t r q : Fin K} (htr : t ≠ r) (htq : t ≠ q) (hrq : r ≠ q) :
    ∀ (l : List Bool) (s : Stacks K 0), s t = bs l →
      (pushLoop t r q).RunsLe s
        (update (update (update s t []) r ((bs l).reverse ++ s r))
          q (bs (pairs l.reverse) ++ s q))
        (10 * l.length + 1)
  | [], s, hs => by
    refine (RunsLe.loopF (by simp [tops, hs])).of_eq ?_ (by simp)
    funext k; simp only [update_apply]; split_ifs <;> simp_all
  | d :: l, s, hs => by
    refine (RunsLe.loopT (by simp [tops, hs]) (bit1_runs (a := d)
      (by rw [tops_bs s t _ hs]; rfl) ((RunsLe.pop t s).seq ((RunsLe.push r (sym d) _).seq
        ((RunsLe.push q (sym d) _).seq (RunsLe.push q 1 _)))))
      (pushLoop_runs htr htq hrq l _ ?_)).of_eq ?_ (by simp; omega)
    · simp [update_of_ne htr, update_of_ne htq, hs]
    · funext k
      simp only [update_apply]
      split_ifs <;> simp_all [pairs_append, bs_append]

/-- Push the value of the register `r` onto the number stack `q` (helper `t`). -/
def nsPush (r q t : Fin K) : Prog K 0 :=
  seq (moveAll r t) (seq (push q 0) (pushLoop t r q))

lemma nsPush_runs {r q t : Fin K} (hrq : r ≠ q) (hrt : r ≠ t) (hqt : q ≠ t) {s : Stacks K 0}
    {v : ℕ} (hr : s r = nst v) (ht : s t = []) :
    (nsPush r q t).RunsLe s (update s q (bs (encodeNat v) ++ s q))
      (16 * (Nat.bits v).length + 5) := by
  have c1 := moveAll_runs hrt (m := 0) (nst v) s hr
  have c2 := RunsLe.push q 0 (update (update s r []) t ((nst v).reverse ++ s t))
  have c3 := pushLoop_runs hrt.symm hqt.symm hrq (Nat.bits v).reverse
    (update (update (update s r []) t ((nst v).reverse ++ s t)) q
      (0 :: update (update s r []) t ((nst v).reverse ++ s t) q))
    (by simp [update_of_ne hqt.symm, ht, nst, bs_reverse])
  refine (c1.seq (c2.seq c3)).of_eq ?_ ?_
  · funext k
    simp only [update_apply]
    split_ifs <;> simp_all [nst, bs_reverse, encodeNat_eq_pairs, bs_append]
  · simp [nst]; omega

/-! ## Pop -/

/-- Read the pair codes `1 d` on top of `q`, pushing the digits onto `t`. -/
def popLoop (q t : Fin K) : Prog K 0 :=
  loop (fun u => u q == some 1) (seq (pop q) (bit1 q fun d => seq (pop q) (push t (sym d))))

lemma popLoop_runs {q t : Fin K} (hqt : q ≠ t) (L : List Sym) :
    ∀ (l : List Bool) (s : Stacks K 0), s q = bs (pairs l) ++ 0 :: L →
      (popLoop q t).RunsLe s (update (update s q (0 :: L)) t ((bs l).reverse ++ s t))
        (7 * l.length + 1)
  | [], s, hs => by
    refine (RunsLe.loopF (by simp [tops, hs])).of_eq ?_ (by simp)
    funext k; simp only [update_apply]; split_ifs <;> simp_all
  | d :: l, s, hs => by
    have hs1 : update s q (s q).tail q = bs (d :: pairs l) ++ 0 :: L := by
      simp [hs]
    refine (RunsLe.loopT (by simp [tops, hs]) ((RunsLe.pop q s).seq (bit1_runs (a := d)
      (by cases d <;> simp [tops, hs, bs])
      ((RunsLe.pop q _).seq (RunsLe.push t (sym d) _))))
      (popLoop_runs hqt L l _ ?_)).of_eq ?_ (by simp; omega)
    · simp [update_of_ne hqt, hs]
    · funext k
      simp only [update_apply]
      split_ifs <;> simp_all

/-- Pop the top number of `q` into the register `r` (helper `t`). -/
def nsPop (q r t : Fin K) : Prog K 0 :=
  seq (clear r) (seq (popLoop q t) (seq (pop q) (moveAll t r)))

lemma nsPop_runs {q r t : Fin K} (hqr : q ≠ r) (hqt : q ≠ t) (hrt : r ≠ t) {s : Stacks K 0}
    {v : ℕ} {L : List Sym} (hq : s q = bs (encodeNat v) ++ L) (ht : s t = []) :
    (nsPop q r t).RunsLe s (update (update s q L) r (nst v))
      (2 * (s r).length + 13 * (Nat.bits v).length + 5) := by
  have c1 := clear_runs r (s r) s rfl
  have c2 := popLoop_runs hqt L (Nat.bits v) (update s r [])
    (by simp [update_of_ne hqr, hq, encodeNat_eq_pairs, bs_append])
  have c3 := RunsLe.pop q (update (update (update s r []) q (0 :: L)) t
    ((bs (Nat.bits v)).reverse ++ update s r [] t))
  have c4 := moveAll_runs (m := 0) hrt.symm (bs (Nat.bits v)).reverse
    (update (update (update (update s r []) q (0 :: L)) t
      ((bs (Nat.bits v)).reverse ++ update s r [] t)) q
      ((update (update (update s r []) q (0 :: L)) t
        ((bs (Nat.bits v)).reverse ++ update s r [] t)) q).tail)
    (by simp [update_of_ne hqt.symm, update_of_ne hrt.symm, ht])
  refine (c1.seq (c2.seq (c3.seq c4))).of_eq ?_ ?_
  · funext k
    simp only [update_apply]
    split_ifs <;> simp_all [nst]
  · simp; omega

end Lax119563Proofs.Compiler
