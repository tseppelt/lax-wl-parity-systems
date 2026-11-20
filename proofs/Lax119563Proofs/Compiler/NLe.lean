import Lax119563Proofs.Compiler.NProg
import Lax119563Proofs.Reduction.SStm

/-!
# Runs of register programs with number stacks within a cost

* `NLe x w p st st' T`: `p` runs from `st` to `st'` within cost `T` (with the combinators of
  `Reduction.HLe`);
* `NSt.Bdd w st`: all registers and all stack entries are below `2 ^ w`, kept by runs
  (`NLe.bounded`);
* `HProg.toN`: the embedding of register programs without stacks (`HLe.toN`), so that the
  expression compiler `Reduction.Ex.code` can be reused.
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

variable {R Q : ℕ} {x : List Bool} {w : ℕ}

/-- `p` runs from `st` to `st'` within cost `T`. -/
def NLe (x : List Bool) (w : ℕ) (p : NProg R Q) (st st' : NSt R Q) (T : ℕ) : Prop :=
  ∃ t ≤ T, NRuns x w p st st' t

namespace NLe

variable {p q : NProg R Q} {st st' st₁ st₂ st₃ : NSt R Q} {T T' T₁ T₂ : ℕ}

lemma of_runs {t : ℕ} (h : NRuns x w p st st' t) : NLe x w p st st' t := ⟨t, le_rfl, h⟩

lemma mono (h : NLe x w p st st' T) (hT : T ≤ T') : NLe x w p st st' T' := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t, by omega, h⟩

lemma seq (h₁ : NLe x w p st₁ st₂ T₁) (h₂ : NLe x w q st₂ st₃ T₂) :
    NLe x w (.seq p q) st₁ st₃ (T₁ + T₂) := by
  obtain ⟨t₁, ht₁, h₁⟩ := h₁; obtain ⟨t₂, ht₂, h₂⟩ := h₂
  exact ⟨t₁ + t₂, by omega, .seq h₁ h₂⟩

lemma iteT {c} (hc : c st.view = true) (h : NLe x w p st st' T) :
    NLe x w (.ite c p q) st st' (T + 1) := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t + 1, by omega, .iteT hc h⟩

lemma iteF {c} (hc : c st.view = false) (h : NLe x w q st st' T) :
    NLe x w (.ite c p q) st st' (T + 1) := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t + 1, by omega, .iteF hc h⟩

lemma loopF {c} (hc : c st.view = false) : NLe x w (.loop c p) st st 1 := of_runs (.loopF hc)

lemma loopT {c} (hc : c st₁.view = true) (h₁ : NLe x w p st₁ st₂ T₁)
    (h₂ : NLe x w (.loop c p) st₂ st₃ T₂) : NLe x w (.loop c p) st₁ st₃ (T₁ + T₂ + 1) := by
  obtain ⟨t₁, ht₁, h₁⟩ := h₁; obtain ⟨t₂, ht₂, h₂⟩ := h₂
  exact ⟨t₁ + t₂ + 1, by omega, .loopT hc h₁ h₂⟩

end NLe

/-! ## Bounded states -/

/-- All registers and all stack entries are below `2 ^ w`. -/
def NSt.Bdd (w : ℕ) (st : NSt R Q) : Prop :=
  (∀ r, st.env r < 2 ^ w) ∧ ∀ q, ∀ v ∈ st.stk q, v < 2 ^ w

lemma NRuns.bounded {p : NProg R Q} {st st' : NSt R Q} {t : ℕ} (h : NRuns x w p st st' t)
    (hw : 2 ≤ w) (hb : st.Bdd w) : st'.Bdd w := by
  have h2 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have h4 : (4 : ℕ) ≤ 2 ^ w := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  induction h with
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hb)
  | iteT _ _ ih => exact ih hb
  | iteF _ _ ih => exact ih hb
  | loopF => exact hb
  | loopT _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hb)
  | emit => exact hb
  | rst => exact hb
  | clr =>
    refine ⟨fun q => ?_, hb.2⟩; simp only [NSt.set_env, Function.update_apply]; split_ifs
    · positivity
    · exact hb.1 q
  | one h' =>
    refine ⟨fun q => ?_, hb.2⟩; simp only [NSt.set_env, Function.update_apply]; split_ifs
    · exact h'
    · exact hb.1 q
  | dbl h' =>
    refine ⟨fun q => ?_, hb.2⟩; simp only [NSt.set_env, Function.update_apply]; split_ifs
    · exact h'
    · exact hb.1 q
  | half h' =>
    refine ⟨fun q => ?_, hb.2⟩; simp only [NSt.set_env, Function.update_apply]; split_ifs
    · exact lt_of_le_of_lt (Nat.div_le_self _ _) h'
    · exact hb.1 q
  | copy _ h' =>
    refine ⟨fun q => ?_, hb.2⟩; simp only [NSt.set_env, Function.update_apply]; split_ifs
    · exact h'
    · exact hb.1 q
  | add _ h' =>
    refine ⟨fun q => ?_, hb.2⟩; simp only [NSt.set_env, Function.update_apply]; split_ifs
    · exact h'
    · exact hb.1 q
  | lt =>
    refine ⟨fun q => ?_, hb.2⟩; simp only [NSt.set_env, Function.update_apply]; split_ifs
    · omega
    · omega
    · exact hb.1 q
  | rd =>
    refine ⟨fun q => ?_, hb.2⟩; simp only [NSt.set_env, Function.update_apply]; split_ifs
    · exact lt_of_le_of_lt (inBit_le _ _) (by omega)
    · exact hb.1 q
  | @spush q r st h' =>
    refine ⟨hb.1, fun q' v hv => ?_⟩
    simp only [NSt.setS_stk, Function.update_apply] at hv
    split_ifs at hv with hq
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact h'
      · subst hq; exact hb.2 _ v hv
    · exact hb.2 q' v hv
  | @spop q r st v vs _ hs hv =>
    refine ⟨fun r' => ?_, fun q' u hu => ?_⟩
    · simp only [NSt.set_env, NSt.setS_env, Function.update_apply]; split_ifs
      · exact hv
      · exact hb.1 r'
    · simp only [NSt.set_stk, NSt.setS_stk, Function.update_apply] at hu
      split_ifs at hu with hq
      · subst hq; exact hb.2 _ u (by rw [hs]; exact List.mem_cons_of_mem _ hu)
      · exact hb.2 q' u hu

lemma NLe.bounded {p : NProg R Q} {st st' : NSt R Q} {T : ℕ} (h : NLe x w p st st' T)
    (hw : 2 ≤ w) (hb : st.Bdd w) : st'.Bdd w := by
  obtain ⟨t, -, h⟩ := h; exact h.bounded hw hb

lemma NLe.pos_le {p : NProg R Q} {st st' : NSt R Q} {T : ℕ} (h : NLe x w p st st' T)
    (hp : st.pos ≤ x.length) : st'.pos ≤ x.length := by
  obtain ⟨t, -, h⟩ := h; exact h.pos_le hp

/-! ## Embedding programs without stacks -/

/-- A program without stacks as a program with stacks. -/
def _root_.Lax119563Proofs.Reduction.HProg.toN : HProg R → NProg R Q
  | .clr r => .clr r
  | .one r => .one r
  | .dbl r => .dbl r
  | .half r => .half r
  | .copy r s => .copy r s
  | .add r s => .add r s
  | .lt f a b => .lt f a b
  | .emit r => .emit r
  | .rd r => .rd r
  | .rst => .rst
  | .seq p q => .seq p.toN q.toN
  | .ite c p q => .ite (fun v => c v.1) p.toN q.toN
  | .loop c p => .loop (fun v => c v.1) p.toN

/-- The register part of a state. -/
def NSt.toH (st : NSt R Q) : HSt R := ⟨st.env, st.pos, st.out⟩

/-- A register state with stacks. -/
def NSt.ofH (st : HSt R) (S : Fin Q → List ℕ) : NSt R Q := ⟨st.env, S, st.pos, st.out⟩

@[simp] lemma NSt.ofH_toH (st : NSt R Q) : NSt.ofH st.toH st.stk = st := rfl
@[simp] lemma NSt.toH_env (st : NSt R Q) : st.toH.env = st.env := rfl
@[simp] lemma NSt.toH_pos (st : NSt R Q) : st.toH.pos = st.pos := rfl
@[simp] lemma NSt.toH_out (st : NSt R Q) : st.toH.out = st.out := rfl
@[simp] lemma NSt.ofH_env (st : HSt R) (S : Fin Q → List ℕ) : (NSt.ofH st S).env = st.env := rfl
@[simp] lemma NSt.ofH_stk (st : HSt R) (S : Fin Q → List ℕ) : (NSt.ofH st S).stk = S := rfl
@[simp] lemma NSt.ofH_pos (st : HSt R) (S : Fin Q → List ℕ) : (NSt.ofH st S).pos = st.pos := rfl
@[simp] lemma NSt.ofH_out (st : HSt R) (S : Fin Q → List ℕ) : (NSt.ofH st S).out = st.out := rfl

lemma _root_.Lax119563Proofs.Reduction.HRuns.toN {p : HProg R} {st st' : HSt R} {t : ℕ} (h : HRuns x w p st st' t)
    (S : Fin Q → List ℕ) : NRuns x w p.toN (NSt.ofH st S) (NSt.ofH st' S) t := by
  induction h with
  | clr h => exact NRuns.clr (st := NSt.ofH _ S) h
  | one h => exact NRuns.one (st := NSt.ofH _ S) h
  | dbl h => exact NRuns.dbl (st := NSt.ofH _ S) h
  | half h => exact NRuns.half (st := NSt.ofH _ S) h
  | copy h1 h2 h3 => exact NRuns.copy (st := NSt.ofH _ S) h1 h2 h3
  | add h1 h2 => exact NRuns.add (st := NSt.ofH _ S) h1 h2
  | lt h1 h2 h3 h4 h5 h6 => exact NRuns.lt (st := NSt.ofH _ S) h1 h2 h3 h4 h5 h6
  | emit h => exact NRuns.emit (st := NSt.ofH _ S) h
  | rd h1 h2 => exact NRuns.rd (st := NSt.ofH _ S) h1 h2
  | rst h => exact NRuns.rst (st := NSt.ofH _ S) h
  | seq _ _ ih₁ ih₂ => exact NRuns.seq ih₁ ih₂
  | @iteT c _ _ _ _ _ hc _ ih => exact NRuns.iteT (c := fun v => c v.1) hc ih
  | @iteF c _ _ _ _ _ hc _ ih => exact NRuns.iteF (c := fun v => c v.1) hc ih
  | @loopF c _ _ hc => exact NRuns.loopF (c := fun v => c v.1) hc
  | @loopT c _ _ _ _ _ _ hc _ _ ih₁ ih₂ => exact NRuns.loopT (c := fun v => c v.1) hc ih₁ ih₂

lemma _root_.Lax119563Proofs.Reduction.HLe.toN {p : HProg R} {st : NSt R Q} {st' : HSt R} {T : ℕ} (h : HLe x w p st.toH st' T) :
    NLe x w p.toN st (NSt.ofH st' st.stk) T := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t, ht, h.toN st.stk⟩

lemma NSt.Bdd.toH {st : NSt R Q} (h : st.Bdd w) : st.toH.Bdd w := h.1

end Lax119563Proofs.Compiler
