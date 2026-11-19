import Lax119563Proofs.Compiler.CSortLoop

/-!
# Syntactic frames of statements

`wReg r c`, `wStk q c`, `wOut c`, `wPos c`: whether the statement `c` contains an
instruction writing the register `r`, the stack `q`, the output, the cursor. If not, the
denotation keeps that part of the state (`exec_env_of`, `exec_stk_of`, `exec_out_of`,
`exec_pos_of`); for concrete programs the flags are computed by `decide`.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool}

namespace CStm

/-- `c` may write register `r`. -/
def wReg (r : Fin R) : CStm R Q → Bool
  | skip => false
  | set r' _ => decide (r' = r)
  | emit _ => false
  | push _ _ => false
  | pop _ r' => decide (r' = r)
  | sne r' _ => decide (r' = r)
  | rd r' => decide (r' = r)
  | rst => false
  | seq p q => wReg r p || wReg r q
  | ite _ p q => wReg r p || wReg r q
  | loop _ b => wReg r b

/-- `c` may write stack `q`. -/
def wStk (q : Fin Q) : CStm R Q → Bool
  | push q' _ => decide (q' = q)
  | pop q' _ => decide (q' = q)
  | seq p p' => wStk q p || wStk q p'
  | ite _ p p' => wStk q p || wStk q p'
  | loop _ b => wStk q b
  | _ => false

/-- `c` may emit. -/
def wOut : CStm R Q → Bool
  | emit _ => true
  | seq p q => wOut p || wOut q
  | ite _ p q => wOut p || wOut q
  | loop _ b => wOut b
  | _ => false

/-- `c` may move the cursor. -/
def wPos : CStm R Q → Bool
  | rd _ => true
  | rst => true
  | seq p q => wPos p || wPos q
  | ite _ p q => wPos p || wPos q
  | loop _ b => wPos b
  | _ => false

lemma iterate_pres {α β : Type*} {f : α → α} {g : α → β} (h : ∀ a, g (f a) = g a) :
    ∀ (n : ℕ) (a : α), g (f^[n] a) = g a
  | 0, _ => rfl
  | n + 1, a => by rw [Function.iterate_succ_apply, iterate_pres h n (f a), h]

open Classical in
lemma exec_loop_cases (c : Ex R) (b : CStm R Q) (st : NSt R Q) :
    ∃ n, exec x (loop c b) st = (exec x b)^[n] st := by
  simp only [exec]
  split
  · exact ⟨_, rfl⟩
  · exact ⟨0, rfl⟩

theorem exec_env_of {r : Fin R} : ∀ (c : CStm R Q) (st : NSt R Q), wReg r c = false →
    (exec x c st).env r = st.env r
  | skip, _, _ => rfl
  | set r' e, st, h => by
    simp only [wReg, decide_eq_false_iff_not] at h
    simp [exec, Function.update_of_ne (Ne.symm h)]
  | emit _, _, _ => rfl
  | push _ _, _, _ => rfl
  | pop q r', st, h => by
    simp only [wReg, decide_eq_false_iff_not] at h
    simp [exec, Function.update_of_ne (Ne.symm h)]
  | sne r' q, st, h => by
    simp only [wReg, decide_eq_false_iff_not] at h
    simp [exec, Function.update_of_ne (Ne.symm h)]
  | rd r', st, h => by
    simp only [wReg, decide_eq_false_iff_not] at h
    simp [exec, Function.update_of_ne (Ne.symm h)]
  | rst, _, _ => rfl
  | seq p q, st, h => by
    simp only [wReg, Bool.or_eq_false_iff] at h
    simp only [exec]; rw [exec_env_of q _ h.2, exec_env_of p _ h.1]
  | ite c p q, st, h => by
    simp only [wReg, Bool.or_eq_false_iff] at h
    simp only [exec]; split
    · exact exec_env_of p _ h.1
    · exact exec_env_of q _ h.2
  | loop c b, st, h => by
    obtain ⟨n, hn⟩ := exec_loop_cases (x := x) c b st
    rw [hn]
    exact iterate_pres (g := fun s : NSt R Q => s.env r) (fun a => exec_env_of b a h) n st

theorem exec_stk_of {q : Fin Q} : ∀ (c : CStm R Q) (st : NSt R Q), wStk q c = false →
    (exec x c st).stk q = st.stk q
  | skip, _, _ => rfl
  | set _ _, _, _ => rfl
  | emit _, _, _ => rfl
  | push q' e, st, h => by
    simp only [wStk, decide_eq_false_iff_not] at h
    simp [exec, Function.update_of_ne (Ne.symm h)]
  | pop q' r, st, h => by
    simp only [wStk, decide_eq_false_iff_not] at h
    simp [exec, Function.update_of_ne (Ne.symm h)]
  | sne _ _, _, _ => rfl
  | rd _, _, _ => rfl
  | rst, _, _ => rfl
  | seq p p', st, h => by
    simp only [wStk, Bool.or_eq_false_iff] at h
    simp only [exec]; rw [exec_stk_of p' _ h.2, exec_stk_of p _ h.1]
  | ite c p p', st, h => by
    simp only [wStk, Bool.or_eq_false_iff] at h
    simp only [exec]; split
    · exact exec_stk_of p _ h.1
    · exact exec_stk_of p' _ h.2
  | loop c b, st, h => by
    obtain ⟨n, hn⟩ := exec_loop_cases (x := x) c b st
    rw [hn]
    exact iterate_pres (g := fun s : NSt R Q => s.stk q) (fun a => exec_stk_of b a h) n st

theorem exec_out_of : ∀ (c : CStm R Q) (st : NSt R Q), wOut c = false →
    (exec x c st).out = st.out
  | skip, _, _ => rfl
  | set _ _, _, _ => rfl
  | emit _, _, h => by simp [wOut] at h
  | push _ _, _, _ => rfl
  | pop _ _, _, _ => rfl
  | sne _ _, _, _ => rfl
  | rd _, _, _ => rfl
  | rst, _, _ => rfl
  | seq p q, st, h => by
    simp only [wOut, Bool.or_eq_false_iff] at h
    simp only [exec]; rw [exec_out_of q _ h.2, exec_out_of p _ h.1]
  | ite c p q, st, h => by
    simp only [wOut, Bool.or_eq_false_iff] at h
    simp only [exec]; split
    · exact exec_out_of p _ h.1
    · exact exec_out_of q _ h.2
  | loop c b, st, h => by
    obtain ⟨n, hn⟩ := exec_loop_cases (x := x) c b st
    rw [hn]
    exact iterate_pres (g := fun s : NSt R Q => s.out) (fun a => exec_out_of b a h) n st

theorem exec_pos_of : ∀ (c : CStm R Q) (st : NSt R Q), wPos c = false →
    (exec x c st).pos = st.pos
  | skip, _, _ => rfl
  | set _ _, _, _ => rfl
  | emit _, _, _ => rfl
  | push _ _, _, _ => rfl
  | pop _ _, _, _ => rfl
  | sne _ _, _, _ => rfl
  | rd _, _, h => by simp [wPos] at h
  | rst, _, h => by simp [wPos] at h
  | seq p q, st, h => by
    simp only [wPos, Bool.or_eq_false_iff] at h
    simp only [exec]; rw [exec_pos_of q _ h.2, exec_pos_of p _ h.1]
  | ite c p q, st, h => by
    simp only [wPos, Bool.or_eq_false_iff] at h
    simp only [exec]; split
    · exact exec_pos_of p _ h.1
    · exact exec_pos_of q _ h.2
  | loop c b, st, h => by
    obtain ⟨n, hn⟩ := exec_loop_cases (x := x) c b st
    rw [hn]
    exact iterate_pres (g := fun s : NSt R Q => s.pos) (fun a => exec_pos_of b a h) n st

/-! ## Frames of `Good` statements -/

variable {w : ℕ} {c : CStm R Q} {st st' : NSt R Q} {T : ℕ}

lemma Good.env_of (h : Good x w c st st' T) {r : Fin R} (hr : wReg r c = false) :
    st'.env r = st.env r := by rw [← h.2.1]; exact exec_env_of c st hr

lemma Good.stk_of (h : Good x w c st st' T) {q : Fin Q} (hq : wStk q c = false) :
    st'.stk q = st.stk q := by rw [← h.2.1]; exact exec_stk_of c st hq

lemma Good.out_of (h : Good x w c st st' T) (ho : wOut c = false) : st'.out = st.out := by
  rw [← h.2.1]; exact exec_out_of c st ho

lemma Good.pos_of (h : Good x w c st st' T) (hp : wPos c = false) : st'.pos = st.pos := by
  rw [← h.2.1]; exact exec_pos_of c st hp

end CStm

end Lax119563Proofs.Compiler
