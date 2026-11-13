import Lax119563Proofs.Hierarchy.Programs
import Lax119563Proofs.Reduction.StackOut

/-!
# Head positions of stack programs

`Prog.RunsLeH`: runs with head positions (`Prog.RunsH`) within a cost bound. A program that
never pushes or pops stack `i` (`Prog.Avoids i`) leaves the head of tape `i` in place, so its
stack-level runs (`RunsLe`) lift to runs with heads. Moving symbols off or onto a stack moves
its head by the number of symbols moved.
-/

open Function

namespace Lax119563Proofs.Reduction

open Hierarchy Hierarchy.Prog

variable {K m : ℕ}

namespace Prog

/-- `p` runs from `x` to `x'` (stacks with heads) within cost `T`. -/
def RunsLeH (p : Hierarchy.Prog K m) (x x' : SH K m) (T : ℕ) : Prop :=
  ∃ t ≤ T, RunsH p x x' t

lemma RunsLeH.mono {p : Hierarchy.Prog K m} {x x' : SH K m} {T T' : ℕ} (h : RunsLeH p x x' T)
    (hT : T ≤ T') : RunsLeH p x x' T' := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t, by omega, h⟩

lemma RunsLeH.seq {p q : Hierarchy.Prog K m} {x₁ x₂ x₃ : SH K m} {T₁ T₂ : ℕ}
    (h₁ : RunsLeH p x₁ x₂ T₁) (h₂ : RunsLeH q x₂ x₃ T₂) :
    RunsLeH (.seq p q) x₁ x₃ (T₁ + T₂) := by
  obtain ⟨t₁, ht₁, h₁⟩ := h₁; obtain ⟨t₂, ht₂, h₂⟩ := h₂
  exact ⟨t₁ + t₂, by omega, .seq h₁ h₂⟩

lemma RunsLeH.iteT {c} {p q : Hierarchy.Prog K m} {x x' : SH K m} {T : ℕ}
    (hc : c (tops x.1) = true) (h : RunsLeH p x x' T) : RunsLeH (.ite c p q) x x' (T + 1) := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t + 1, by omega, .iteT hc h⟩

lemma RunsLeH.iteF {c} {p q : Hierarchy.Prog K m} {x x' : SH K m} {T : ℕ}
    (hc : c (tops x.1) = false) (h : RunsLeH q x x' T) : RunsLeH (.ite c p q) x x' (T + 1) := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t + 1, by omega, .iteF hc h⟩

lemma RunsLeH.loopF {c} {p : Hierarchy.Prog K m} {x : SH K m} (hc : c (tops x.1) = false) :
    RunsLeH (.loop c p) x x 1 := ⟨1, le_rfl, .loopF hc⟩

lemma RunsLeH.loopT {c} {p : Hierarchy.Prog K m} {x₁ x₂ x₃ : SH K m} {T₁ T₂ : ℕ}
    (hc : c (tops x₁.1) = true) (h₁ : RunsLeH p x₁ x₂ T₁) (h₂ : RunsLeH (.loop c p) x₂ x₃ T₂) :
    RunsLeH (.loop c p) x₁ x₃ (T₁ + T₂ + 1) := by
  obtain ⟨t₁, ht₁, h₁⟩ := h₁; obtain ⟨t₂, ht₂, h₂⟩ := h₂
  exact ⟨t₁ + t₂ + 1, by omega, .loopT hc h₁ h₂⟩

lemma RunsLeH.of_eq {p : Hierarchy.Prog K m} {x x₁ x₂ : SH K m} {T T' : ℕ}
    (h : RunsLeH p x x₁ T) (hx : x₁ = x₂) (hT : T ≤ T') : RunsLeH p x x₂ T' :=
  hx ▸ h.mono hT

lemma RunsLeH.runsLe {p : Hierarchy.Prog K m} {x x' : SH K m} {T : ℕ} (h : RunsLeH p x x' T) :
    p.RunsLe x.1 x'.1 T := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t, ht, h.runs⟩

/-- `p` never pushes or pops stack `i`. -/
def Avoids (i : Fin K) : Hierarchy.Prog K m → Prop
  | .skip => True
  | .push j _ => j ≠ i
  | .pop j => j ≠ i
  | .seq p q => Avoids i p ∧ Avoids i q
  | .ite _ p q => Avoids i p ∧ Avoids i q
  | .loop _ p => Avoids i p

lemma RunsH.head_of_avoids {i : Fin K} {p : Hierarchy.Prog K m} {x x' : SH K m} {t : ℕ}
    (h : RunsH p x x' t) (ha : Avoids i p) : x'.2 i = x.2 i := by
  induction h with
  | skip => rfl
  | push => simp [update_of_ne (show i ≠ _ from fun e => ha e.symm)]
  | pop => simp [update_of_ne (show i ≠ _ from fun e => ha e.symm)]
  | seq _ _ ih₁ ih₂ => exact (ih₂ ha.2).trans (ih₁ ha.1)
  | iteT _ _ ih => exact ih ha.1
  | iteF _ _ ih => exact ih ha.2
  | loopF => rfl
  | loopT _ _ _ ih₁ ih₂ => exact (ih₂ ha).trans (ih₁ ha)

/-- A run of a program avoiding `i` lifts to a run with heads keeping the head of `i`. -/
lemma RunsLe.toH {i : Fin K} {p : Hierarchy.Prog K m} {s s' : Stacks K m} {T : ℕ}
    (h : p.RunsLe s s' T) (ha : Avoids i p) (hd : Fin K → ℤ) :
    ∃ hd', hd' i = hd i ∧ RunsLeH p (s, hd) (s', hd') T := by
  obtain ⟨t, ht, h⟩ := h
  obtain ⟨hd', h'⟩ := Runs.runsH h hd
  exact ⟨hd', h'.head_of_avoids ha, t, ht, h'⟩

/-! ## Moving symbols with heads -/

lemma pushTopOf_runsH (i j : Fin K) {s : Stacks K m} {hd : Fin K → ℤ} {a : Fin (m + 2)}
    (ha : tops s i = some a) :
    ∀ as : List (Fin (m + 2)), a ∈ as →
      RunsLeH (pushTopOf i j as) (s, hd) (update s j (a :: s j), update hd j (hd j - 1))
        (as.length + 2)
  | [], h => by simp at h
  | b :: as, h => by
    by_cases hb : b = a
    · subst hb
      exact (RunsLeH.iteT (by simp [ha]) ⟨2, le_rfl, RunsH.push⟩).mono (by simp)
    · have : a ∈ as := by simp at h; tauto
      exact ((pushTopOf_runsH i j ha as this).iteF (by simp [ha, Ne.symm hb])).mono (by simp)

lemma moveOne_runsH {i j : Fin K} (hij : i ≠ j) {s : Stacks K m} {hd : Fin K → ℤ}
    {a : Fin (m + 2)} {l : List (Fin (m + 2))} (hs : s i = a :: l) :
    RunsLeH (moveOne i j) (s, hd)
      (update (update s i l) j (a :: s j), update (update hd i (hd i + 1)) j (hd j - 1))
      (m + 5) := by
  have h1 := pushTopOf_runsH i j (s := s) (hd := hd) (by simp [tops, hs])
    (List.finRange (m + 2)) (List.mem_finRange a)
  have h2 : RunsLeH (pop i) (update s j (a :: s j), update hd j (hd j - 1))
      (update (update s j (a :: s j)) i (update s j (a :: s j) i).tail,
        update (update hd j (hd j - 1)) i (update hd j (hd j - 1) i + 1)) 1 :=
    ⟨1, le_rfl, RunsH.pop⟩
  refine (h1.seq h2).of_eq ?_ (by simp)
  refine Prod.ext ?_ ?_
  · funext k; simp only [update_apply]; split_ifs <;> simp_all
  · funext k; simp only [update_apply]; split_ifs <;> simp_all

lemma moveAll_runsH {i j : Fin K} (hij : i ≠ j) :
    ∀ (l : List (Fin (m + 2))) (s : Stacks K m) (hd : Fin K → ℤ), s i = l →
      RunsLeH (moveAll i j) (s, hd)
        (update (update s i []) j (l.reverse ++ s j),
          update (update hd i (hd i + l.length)) j (hd j - l.length))
        ((m + 6) * l.length + 1)
  | [], s, hd, hs => by
    refine (RunsLeH.loopF (p := moveOne i j) (c := fun r => (r i).isSome) (x := (s, hd))
      (by simp [tops, hs])).of_eq ?_ (by simp)
    refine Prod.ext ?_ ?_
    · funext k; simp only [update_apply]; split_ifs <;> simp_all
    · funext k; simp only [update_apply]; split_ifs <;> simp_all
  | a :: l, s, hd, hs => by
    have h1 := moveOne_runsH hij (hd := hd) hs
    have h2 := moveAll_runsH hij l (update (update s i l) j (a :: s j))
      (update (update hd i (hd i + 1)) j (hd j - 1)) (by simp [update_of_ne hij])
    refine (RunsLeH.loopT (c := fun r => (r i).isSome) (by simp [tops, hs]) h1 h2).of_eq ?_
      (le_of_eq (by simp only [List.length_cons]; ring))
    refine Prod.ext ?_ ?_
    · funext k; simp only [update_apply]; split_ifs <;> simp_all
    · funext k
      simp only [update_apply, List.length_cons]
      split_ifs <;> simp_all <;> push_cast <;> ring

end Prog

end Lax119563Proofs.Reduction
