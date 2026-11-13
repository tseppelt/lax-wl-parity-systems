import Lax119563Proofs.Hierarchy.Programs
import Lax119563Proofs.Reduction.Bits

/-!
# Binary registers on stacks

Stack programs over the symbols `Fin 2` (`m = 0`) implementing the primitive instructions of
`HProg` on numbers stored as their binary digits, least significant digit on top
(`nst v = (Nat.bits v).map sym`). Every routine is specified for arbitrary stacks: it changes
only the stacks named in its conclusion and restores its empty helper stacks.
-/

open Function

namespace Lax119563Proofs.Reduction

open Hierarchy Hierarchy.Prog
open Machines (valBits valBits_bits)

/-- Stack symbols. -/
abbrev Sym := Fin (0 + 2)

/-- A bit as a stack symbol. -/
def sym (b : Bool) : Sym := if b then 1 else 0

@[simp] lemma sym_true : sym true = 1 := rfl
@[simp] lemma sym_false : sym false = 0 := rfl

lemma sym_eq_one (b : Bool) : (sym b == 1) = b := by cases b <;> rfl

/-- A list of bits as stack symbols. -/
def bs (l : List Bool) : List Sym := l.map sym

/-- The stack of a number: its binary digits, least significant on top. -/
def nst (v : ℕ) : List Sym := bs (Nat.bits v)

@[simp] lemma bs_nil : bs [] = [] := rfl
@[simp] lemma bs_cons (b : Bool) (l : List Bool) : bs (b :: l) = sym b :: bs l := rfl
@[simp] lemma length_bs (l : List Bool) : (bs l).length = l.length := List.length_map _
lemma bs_append (l l' : List Bool) : bs (l ++ l') = bs l ++ bs l' := List.map_append
lemma bs_reverse (l : List Bool) : bs l.reverse = (bs l).reverse := List.map_reverse ..

@[simp] lemma nst_zero : nst 0 = [] := by simp [nst]

lemma nst_bit1 (v : ℕ) : nst (2 * v + 1) = 1 :: nst v := by simp [nst, Nat.bit1_bits]

lemma nst_bit0 {v : ℕ} (hv : v ≠ 0) : nst (2 * v) = 0 :: nst v := by
  simp [nst, Nat.bit0_bits v hv]

lemma bits_div_two (v : ℕ) : Nat.bits (v / 2) = (Nat.bits v).tail := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' v
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [Nat.bit0_bits m (by omega)]; simp
  · rw [show (2 * m + 1) / 2 = m by omega, Nat.bit1_bits]; simp

lemma nst_half (v : ℕ) : nst (v / 2) = (nst v).tail := by
  simp [nst, bs, bits_div_two, List.map_tail]

lemma length_nst_le {v w : ℕ} (h : v < 2 ^ w) : (nst v).length ≤ w := by
  simpa [nst] using length_bits_le h

lemma nst_eq_nil_iff (v : ℕ) : nst v = [] ↔ v = 0 := by
  simp [nst, bs, Machines.bits_eq_nil_iff]

lemma head_nst (v : ℕ) :
    ((nst v).head?.map (· == 1)) = if v = 0 then none else some (v % 2 == 1) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' v
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [nst_bit0 (by omega)]; simp; omega
  · rw [nst_bit1]; simp

variable {K : ℕ}

/-! ## Single instructions -/

/-- `r := 2r + 1`. -/
def hOne (r : Fin K) : Prog K 0 := push r 1

lemma hOne_runs (r : Fin K) {s : Stacks K 0} {v : ℕ} (hs : s r = nst v) :
    (hOne r).RunsLe s (update s r (nst (2 * v + 1))) 2 :=
  (RunsLe.push r 1 s).of_eq (by rw [hs, nst_bit1]) le_rfl

/-- `r := 2r`. -/
def hDbl (r : Fin K) : Prog K 0 := ite (fun t => (t r).isSome) (push r 0) skip

lemma hDbl_runs (r : Fin K) {s : Stacks K 0} {v : ℕ} (hs : s r = nst v) :
    (hDbl r).RunsLe s (update s r (nst (2 * v))) 3 := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · refine ((RunsLe.skip s).iteF (by simp [tops, hs])).of_eq ?_ (by norm_num)
    simp only [mul_zero]; rw [← hs]; simp
  · refine ((RunsLe.push r 0 s).iteT ?_).of_eq ?_ le_rfl
    · have : nst v ≠ [] := by rw [Ne, nst_eq_nil_iff]; omega
      simp [tops, hs, Option.isSome_iff_ne_none, List.head?_eq_none_iff, this]
    · rw [hs, nst_bit0 (by omega)]

/-- `r := r / 2`. -/
def hHalf (r : Fin K) : Prog K 0 := pop r

lemma hHalf_runs (r : Fin K) {s : Stacks K 0} {v : ℕ} (hs : s r = nst v) :
    (hHalf r).RunsLe s (update s r (nst (v / 2))) 1 :=
  (RunsLe.pop r s).of_eq (by rw [hs, nst_half]) le_rfl

lemma clear_nst (r : Fin K) {s : Stacks K 0} {v : ℕ} (hs : s r = nst v) :
    (clear r).RunsLe s (update s r (nst 0)) (2 * (nst v).length + 1) :=
  (clear_runs r _ s hs).of_eq (by simp) le_rfl

/-! ## Copying -/

/-- `d := r` through the empty helper `t`. -/
def hCopy (r d t : Fin K) : Prog K 0 := seq (clear d) (seq (moveAll r t) (dupAll t r d))

lemma hCopy_runs {r d t : Fin K} (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t) {s : Stacks K 0}
    {v : ℕ} (hs : s r = nst v) (ht : s t = []) :
    (hCopy r d t).RunsLe s (update s d (nst v))
      (2 * (s d).length + 16 * (nst v).length + 3) := by
  have h1 := clear_runs d (s d) s rfl
  have h2 := moveAll_runs hrt (nst v) (update s d []) (by simp [update_of_ne hrd, hs])
  have h3 := dupAll_runs hrt.symm hdt.symm hrd (m := 0) ((nst v).reverse)
    (update (update (update s d []) r []) t ((nst v).reverse ++ update s d [] t))
    (by simp [update_of_ne hdt.symm, ht])
  refine (h1.seq (h2.seq h3)).of_eq ?_ (by simp; omega)
  funext k
  simp only [update_apply]
  split_ifs <;> simp_all

/-- `d := r` for an empty `d`, leaving the copy reversed on nothing: copy `r` onto the empty
helper `d` through `t` (`d` must be empty). -/
lemma hCopy_runs_empty {r d t : Fin K} (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t)
    {s : Stacks K 0} {v : ℕ} (hs : s r = nst v) (ht : s t = []) (hd : s d = []) :
    (seq (moveAll r t) (dupAll t r d)).RunsLe s (update s d (nst v))
      (16 * (nst v).length + 2) := by
  have h2 := moveAll_runs hrt (nst v) s hs
  have h3 := dupAll_runs hrt.symm hdt.symm hrd (m := 0) ((nst v).reverse)
    (update (update s r []) t ((nst v).reverse ++ s t)) (by simp [ht])
  refine (h2.seq h3).of_eq ?_ (by simp; omega)
  funext k
  simp only [update_apply]
  split_ifs <;> simp_all

/-! ## Case distinctions on top bits -/

/-- Branch on the top bit of `i` (`true` iff the top is `1`). -/
def bit1 (i : Fin K) (f : Bool → Prog K 0) : Prog K 0 :=
  ite (fun t => t i == some 1) (f true) (f false)

lemma bit1_runs {i : Fin K} {f : Bool → Prog K 0} {s s' : Stacks K 0} {T : ℕ} {a : Bool}
    (ha : (tops s i == some 1) = a) (h : (f a).RunsLe s s' T) :
    (bit1 i f).RunsLe s s' (T + 1) := by
  cases a
  · exact h.iteF ha
  · exact h.iteT ha

/-- Branch on the top bits of `i` and `j`. -/
def bit2 (i j : Fin K) (f : Bool → Bool → Prog K 0) : Prog K 0 :=
  bit1 i fun a => bit1 j fun b => f a b

lemma bit2_runs {i j : Fin K} {f : Bool → Bool → Prog K 0} {s s' : Stacks K 0} {T : ℕ}
    {a b : Bool} (ha : (tops s i == some 1) = a) (hb : (tops s j == some 1) = b)
    (h : (f a b).RunsLe s s' T) : (bit2 i j f).RunsLe s s' (T + 2) :=
  bit1_runs ha (bit1_runs hb h)

/-- Branch on the top bits of `i`, `j` and `k`. -/
def bit3 (i j k : Fin K) (f : Bool → Bool → Bool → Prog K 0) : Prog K 0 :=
  bit1 i fun a => bit1 j fun b => bit1 k fun c => f a b c

lemma bit3_runs {i j k : Fin K} {f : Bool → Bool → Bool → Prog K 0} {s s' : Stacks K 0}
    {T : ℕ} {a b c : Bool} (ha : (tops s i == some 1) = a) (hb : (tops s j == some 1) = b)
    (hc : (tops s k == some 1) = c) (h : (f a b c).RunsLe s s' T) :
    (bit3 i j k f).RunsLe s s' (T + 3) :=
  bit1_runs ha (bit1_runs hb (bit1_runs hc h))

lemma tops_bs (s : Stacks K 0) (i : Fin K) (l : List Bool) (hs : s i = bs l) :
    (tops s i == some 1) = l.headD false := by
  cases l with
  | nil => simp [tops, hs]
  | cons b l => cases b <;> simp [tops, hs]

/-! ## Addition -/

/-- The carry as a stack. -/
def carrySt (c : Bool) : List Sym := if c then [1] else []

@[simp] lemma carrySt_true : carrySt true = [1] := rfl
@[simp] lemma carrySt_false : carrySt false = [] := rfl

/-- One step of the ripple-carry adder on `r` and `b` with carry stack `c`, writing the sum
digit onto `o`. -/
def addLeaf (r b c o : Fin K) (x y z : Bool) : Prog K 0 :=
  seq (pop r) (seq (pop b) (seq (pop c) (seq (push o (sym (Bool.xor (Bool.xor x y) z)))
    (if maj x y z then push c 1 else skip))))

/-- The ripple-carry loop. -/
def ripple (r b c o : Fin K) : Prog K 0 :=
  loop (fun t => (t r).isSome || (t b).isSome || (t c).isSome) (bit3 r b c (addLeaf r b c o))

section Ripple

variable {r b c o : Fin K} (hrb : r ≠ b) (hrc : r ≠ c) (hro : r ≠ o) (hbc : b ≠ c)
  (hbo : b ≠ o) (hco : c ≠ o)
include hrb hrc hro hbc hbo hco

lemma addLeaf_runs {s : Stacks K 0} {x y z : Bool} {l l' : List Bool}
    (hr : (s r).tail = bs l) (hb : (s b).tail = bs l') (hc : s c = carrySt z) :
    (addLeaf r b c o x y z).RunsLe s
      (update (update (update (update s r (bs l)) b (bs l')) c (carrySt (maj x y z))) o
        (sym (Bool.xor (Bool.xor x y) z) :: s o)) 7 := by
  have e3 : (s c).tail = [] := by rw [hc]; cases z <;> rfl
  unfold addLeaf
  cases hm : maj x y z
  · simp only [Bool.false_eq_true, if_false, carrySt_false]
    refine ((RunsLe.pop r s).seq ((RunsLe.pop b _).seq ((RunsLe.pop c _).seq
      ((RunsLe.push o _ _).seq (RunsLe.skip _))))).of_eq ?_ (by norm_num)
    funext k
    simp only [update_apply]
    split_ifs <;> simp_all
  · simp only [if_true, carrySt_true]
    refine ((RunsLe.pop r s).seq ((RunsLe.pop b _).seq ((RunsLe.pop c _).seq
      ((RunsLe.push o _ _).seq (RunsLe.push c 1 _))))).of_eq ?_ (by norm_num)
    funext k
    simp only [update_apply]
    split_ifs with h1 h2 h3 h4 h5 h6 h7 <;> subst_vars <;> simp_all

lemma ripple_nil (z : Bool) (s : Stacks K 0) (hr : s r = []) (hb : s b = [])
    (hc : s c = carrySt z) :
    (ripple r b c o).RunsLe s
      (update (update (update (update s r []) b []) c []) o ((bs (addL [] [] z)).reverse ++ s o))
      (11 * (addL [] [] z).length + 1) := by
  cases z
  · refine (RunsLe.loopF (by simp [tops, hr, hb, hc])).of_eq ?_ (by simp [addL])
    funext k
    simp only [update_apply, addL]
    split_ifs <;> simp_all
  · refine (RunsLe.loopT (by simp [tops, hc]) (bit3_runs (a := false) (b := false)
      (c := true) (by rw [tops_bs s r [] hr]; rfl) (by rw [tops_bs s b [] hb]; rfl)
      (by simp [tops, hc]) (addLeaf_runs hrb hrc hro hbc hbo hco (l := []) (l' := [])
        (by simp [hr]) (by simp [hb]) hc))
      (RunsLe.loopF ?_)).of_eq ?_ (by simp [addL])
    · simp [tops, update_of_ne hrb, update_of_ne hrc, update_of_ne hro, update_of_ne hbc,
        update_of_ne hbo, update_of_ne hco, maj]
    · funext k
      simp only [update_apply, addL]
      split_ifs <;> simp_all [maj]

lemma ripple_runs : ∀ (l l' : List Bool) (z : Bool) (s : Stacks K 0), s r = bs l →
    s b = bs l' → s c = carrySt z →
    (ripple r b c o).RunsLe s
      (update (update (update (update s r []) b []) c []) o ((bs (addL l l' z)).reverse ++ s o))
      (11 * (addL l l' z).length + 1)
  | [], [], z, s, hr, hb, hc => ripple_nil hrb hrc hro hbc hbo hco z s hr hb hc
  | x :: l, [], z, s, hr, hb, hc => by
    refine (RunsLe.loopT (by simp [tops, hr]) (bit3_runs (a := x) (b := false)
      (c := z) (by rw [tops_bs s r _ hr]; rfl) (by rw [tops_bs s b [] hb]; rfl)
      (by cases z <;> simp [tops, hc]) (addLeaf_runs hrb hrc hro hbc hbo hco (l := l) (l' := [])
        (by simp [hr]) (by simp [hb]) hc))
      (ripple_runs l [] (x && z) _ ?_ ?_ ?_)).of_eq ?_ (by simp [addL]; omega)
    · simp [update_of_ne hrb, update_of_ne hrc, update_of_ne hro]
    · simp [update_of_ne hbc, update_of_ne hbo]
    · simp [update_of_ne hco, maj]
    · funext k
      simp only [update_apply, addL]
      split_ifs <;> simp_all
  | [], y :: l', z, s, hr, hb, hc => by
    refine (RunsLe.loopT (by simp [tops, hb]) (bit3_runs (a := false) (b := y)
      (c := z) (by rw [tops_bs s r [] hr]; rfl) (by rw [tops_bs s b _ hb]; rfl)
      (by cases z <;> simp [tops, hc]) (addLeaf_runs hrb hrc hro hbc hbo hco (l := []) (l' := l')
        (by simp [hr]) (by simp [hb]) hc))
      (ripple_runs [] l' (y && z) _ ?_ ?_ ?_)).of_eq ?_ (by simp [addL]; omega)
    · simp [update_of_ne hrb, update_of_ne hrc, update_of_ne hro]
    · simp [update_of_ne hbc, update_of_ne hbo]
    · simp [update_of_ne hco, maj]
    · funext k
      simp only [update_apply, addL]
      split_ifs <;> simp_all
  | x :: l, y :: l', z, s, hr, hb, hc => by
    refine (RunsLe.loopT (by simp [tops, hr]) (bit3_runs (a := x) (b := y)
      (c := z) (by rw [tops_bs s r _ hr]; rfl) (by rw [tops_bs s b _ hb]; rfl)
      (by cases z <;> simp [tops, hc]) (addLeaf_runs hrb hrc hro hbc hbo hco (l := l) (l' := l')
        (by simp [hr]) (by simp [hb]) hc))
      (ripple_runs l l' (maj x y z) _ ?_ ?_ ?_)).of_eq ?_ (by simp [addL]; omega)
    · simp [update_of_ne hrb, update_of_ne hrc, update_of_ne hro]
    · simp [update_of_ne hbc, update_of_ne hbo]
    · simp [update_of_ne hco]
    · funext k
      simp only [update_apply, addL]
      split_ifs <;> simp_all
  termination_by l l' => l.length + l'.length

end Ripple

end Lax119563Proofs.Reduction
