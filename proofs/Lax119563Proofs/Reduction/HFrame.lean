import Lax119563Proofs.Reduction.HLib

/-!
# Frame facts for register programs

Syntactic over-approximations of the effects of an `HProg`: the registers it may write
(`HProg.wr`), whether it may emit (`HProg.em`) and whether it may move the input cursor
(`HProg.mv`). A run keeps every register not written, the output if nothing is emitted, and
the cursor if it is not moved. Runs keep all registers below `2 ^ w` (`HRuns.bounded`).
-/

namespace Lax119563Proofs.Reduction

variable {R : ℕ} {x : List Bool} {w : ℕ}

namespace HProg

/-- The registers a program may write. -/
def wr : HProg R → Fin R → Bool
  | .clr r, q => decide (q = r)
  | .one r, q => decide (q = r)
  | .dbl r, q => decide (q = r)
  | .half r, q => decide (q = r)
  | .copy _ s, q => decide (q = s)
  | .add r _, q => decide (q = r)
  | .lt f _ _, q => decide (q = f)
  | .emit _, _ => false
  | .rd r, q => decide (q = r)
  | .rst, _ => false
  | .seq p p', q => p.wr q || p'.wr q
  | .ite _ p p', q => p.wr q || p'.wr q
  | .loop _ p, q => p.wr q

/-- The program may emit. -/
def em : HProg R → Bool
  | .emit _ => true
  | .seq p p' => p.em || p'.em
  | .ite _ p p' => p.em || p'.em
  | .loop _ p => p.em
  | _ => false

/-- The program may move the input cursor. -/
def mv : HProg R → Bool
  | .rd _ => true
  | .rst => true
  | .seq p p' => p.mv || p'.mv
  | .ite _ p p' => p.mv || p'.mv
  | .loop _ p => p.mv
  | _ => false

end HProg

/-- All registers are below `2 ^ w`. -/
def HSt.Bdd (w : ℕ) (st : HSt R) : Prop := ∀ q, st.env q < 2 ^ w

lemma HRuns.frame {p : HProg R} {st st' : HSt R} {t : ℕ} (h : HRuns x w p st st' t) {q : Fin R}
    (hq : p.wr q = false) : st'.env q = st.env q := by
  induction h with
  | seq _ _ ih₁ ih₂ =>
    simp only [HProg.wr, Bool.or_eq_false_iff] at hq
    rw [ih₂ hq.2, ih₁ hq.1]
  | iteT _ _ ih => simp only [HProg.wr, Bool.or_eq_false_iff] at hq; exact ih hq.1
  | iteF _ _ ih => simp only [HProg.wr, Bool.or_eq_false_iff] at hq; exact ih hq.2
  | loopF => rfl
  | loopT _ _ _ ih₁ ih₂ => rw [ih₂ hq, ih₁ hq]
  | emit => rfl
  | rst => rfl
  | _ =>
    simp only [HProg.wr, decide_eq_false_iff_not] at hq
    simp [HSt.set, Function.update_of_ne hq]

lemma HRuns.out_eq {p : HProg R} {st st' : HSt R} {t : ℕ} (h : HRuns x w p st st' t)
    (hp : p.em = false) : st'.out = st.out := by
  induction h with
  | seq _ _ ih₁ ih₂ =>
    simp only [HProg.em, Bool.or_eq_false_iff] at hp
    rw [ih₂ hp.2, ih₁ hp.1]
  | iteT _ _ ih => simp only [HProg.em, Bool.or_eq_false_iff] at hp; exact ih hp.1
  | iteF _ _ ih => simp only [HProg.em, Bool.or_eq_false_iff] at hp; exact ih hp.2
  | loopF => rfl
  | loopT _ _ _ ih₁ ih₂ => rw [ih₂ hp, ih₁ hp]
  | emit => simp [HProg.em] at hp
  | _ => rfl

lemma HRuns.pos_eq {p : HProg R} {st st' : HSt R} {t : ℕ} (h : HRuns x w p st st' t)
    (hp : p.mv = false) : st'.pos = st.pos := by
  induction h with
  | seq _ _ ih₁ ih₂ =>
    simp only [HProg.mv, Bool.or_eq_false_iff] at hp
    rw [ih₂ hp.2, ih₁ hp.1]
  | iteT _ _ ih => simp only [HProg.mv, Bool.or_eq_false_iff] at hp; exact ih hp.1
  | iteF _ _ ih => simp only [HProg.mv, Bool.or_eq_false_iff] at hp; exact ih hp.2
  | loopF => rfl
  | loopT _ _ _ ih₁ ih₂ => rw [ih₂ hp, ih₁ hp]
  | rd => simp [HProg.mv] at hp
  | rst => simp [HProg.mv] at hp
  | _ => rfl

lemma HRuns.bounded {p : HProg R} {st st' : HSt R} {t : ℕ} (h : HRuns x w p st st' t)
    (hw : 1 ≤ w) (hb : st.Bdd w) : st'.Bdd w := by
  have h2 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  induction h with
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hb)
  | iteT _ _ ih => exact ih hb
  | iteF _ _ ih => exact ih hb
  | loopF => exact hb
  | loopT _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hb)
  | emit => exact hb
  | rst => exact hb
  | clr =>
    intro q; simp only [HSt.set, Function.update_apply]; split_ifs
    · positivity
    · exact hb q
  | one h' =>
    intro q; simp only [HSt.set, Function.update_apply]; split_ifs
    · exact h'
    · exact hb q
  | dbl h' =>
    intro q; simp only [HSt.set, Function.update_apply]; split_ifs
    · exact h'
    · exact hb q
  | half h' =>
    intro q; simp only [HSt.set, Function.update_apply]; split_ifs
    · exact lt_of_le_of_lt (Nat.div_le_self _ _) h'
    · exact hb q
  | copy _ h' =>
    intro q; simp only [HSt.set, Function.update_apply]; split_ifs
    · exact h'
    · exact hb q
  | add _ h' =>
    intro q; simp only [HSt.set, Function.update_apply]; split_ifs
    · exact h'
    · exact hb q
  | lt =>
    intro q; simp only [HSt.set, Function.update_apply]; split_ifs
    · omega
    · omega
    · exact hb q
  | rd =>
    intro q; simp only [HSt.set, Function.update_apply]; split_ifs
    · unfold inBit; cases (x.getD _ false) <;> simp; omega
    · exact hb q

lemma HLe.frame {p : HProg R} {st st' : HSt R} {T : ℕ} (h : HLe x w p st st' T) {q : Fin R}
    (hq : p.wr q = false) : st'.env q = st.env q := by
  obtain ⟨t, -, h⟩ := h; exact h.frame hq

lemma HLe.out_eq {p : HProg R} {st st' : HSt R} {T : ℕ} (h : HLe x w p st st' T)
    (hp : p.em = false) : st'.out = st.out := by
  obtain ⟨t, -, h⟩ := h; exact h.out_eq hp

lemma HLe.pos_eq {p : HProg R} {st st' : HSt R} {T : ℕ} (h : HLe x w p st st' T)
    (hp : p.mv = false) : st'.pos = st.pos := by
  obtain ⟨t, -, h⟩ := h; exact h.pos_eq hp

lemma HLe.bounded {p : HProg R} {st st' : HSt R} {T : ℕ} (h : HLe x w p st st' T)
    (hw : 1 ≤ w) (hb : st.Bdd w) : st'.Bdd w := by
  obtain ⟨t, -, h⟩ := h; exact h.bounded hw hb

end Lax119563Proofs.Reduction
