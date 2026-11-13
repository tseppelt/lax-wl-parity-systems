import Lax119563Proofs.Matrix.SpoilerStrip

/-!
# Spoiler's moves through a schema gadget

The whole strip, the link to the end coordinate class, the junction moves, and the five ways
of following an inference backwards through the gadget of a schema (Lemma "Following an
inference" with row sweeps).
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems
open Lax119563.ColoredGraphs Lax119563.PebbleGame

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

local notation "G₀" => matrixGraph I 0
local notation "G₁" => matrixGraph I 1

/-- Replacing every representative. -/
lemma forces_replaceEvery {S : St I} {cls : Fin k → ICls I} {lab : Fin k → Lab}
    (hH : Holds S cls lab) (hPI : IsPartialIso G₀ G₁ S) (newCls : Fin k → ICls I)
    (hval : ∀ i, ClsValid I (newCls i)) (R : Fin k → Lab → Lab → Prop)
    (hR : ∀ (S1 : St I) i q, HoldsAt S1 i.castSucc (cls i) (lab i) →
      S1 spare = some (zv (newCls i) (hval i), q) → IsPartialIso G₀ G₁ S1 →
      R i (lab i) (eff I 1 (nm q))) :
    Forces (2 * k) S fun S' => ∃ lab' : Fin k → Lab, (∀ i, R i (lab i) (lab' i)) ∧
      Holds S' newCls lab' ∧ IsPartialIso G₀ G₁ S' := by
  have := forces_replaceAll (List.finRange k) (List.nodup_finRange k) hH hPI newCls
    (fun i _ => hval i) R fun S1 i q _ h1 h2 h3 => hR S1 i q h1 h2 h3
  rw [List.length_finRange] at this
  exact this.weaken fun S' ⟨lab', h1, _, h3, h4⟩ =>
    ⟨lab', fun i => h1 i (List.mem_finRange i), h3.congr_cls fun i => by simp, h4⟩

variable {e : Fin I.schemas.length} {g : Fin k → Coord k ℓ}

/-! ### The strip -/

/-- The cost of sweeping a strip. -/
def stripCost (e : Fin I.schemas.length) : ℕ :=
  ∑ σ ∈ Finset.range (numSteps k ℓ), (4 * k + 1) * hit e σ

/-- Sweeping the strip forwards, from stage `0` to stage `n`. -/
lemma strip_fwd (hk : 2 ≤ k) (hg : Cols e g) :
    ∀ n ≤ numSteps k ℓ, ∀ (S : St I) (lab : Fin k → Lab),
      Holds S (fun i => trackAt I e (g i) 0) lab → IsPartialIso G₀ G₁ S →
      Forces (∑ σ ∈ Finset.range n, (4 * k + 1) * hit e σ) S fun S' => ∃ lab' : Fin k → Lab,
        Holds S' (fun i => trackAt I e (g i) n) lab' ∧ ∑ i, (lab' i).1 = ∑ i, (lab i).1 ∧
        IsPartialIso G₀ G₁ S'
  | 0, _, S, lab, hH, hPI => Forces.ret ⟨lab, hH, rfl, hPI⟩
  | n + 1, hn, S, lab, hH, hPI => by
    rw [Finset.sum_range_succ]
    refine (strip_fwd hk hg n (by omega) S lab hH hPI).bind fun S1 ⟨lab1, hH1, hs1, hPI1⟩ => ?_
    refine (sweep hk hg (σ := n) (by omega) true (hH1.congr_cls fun i => by simp) hPI1).weaken
      fun S2 ⟨lab2, hH2, hs2, hPI2⟩ => ⟨lab2, hH2.congr_cls fun i => by simp, hs2.trans hs1, hPI2⟩

/-- Sweeping the strip backwards, from stage `n` to stage `0`. -/
lemma strip_bwd (hk : 2 ≤ k) (hg : Cols e g) :
    ∀ n ≤ numSteps k ℓ, ∀ (S : St I) (lab : Fin k → Lab),
      Holds S (fun i => trackAt I e (g i) n) lab → IsPartialIso G₀ G₁ S →
      Forces (∑ σ ∈ Finset.range n, (4 * k + 1) * hit e σ) S fun S' => ∃ lab' : Fin k → Lab,
        Holds S' (fun i => trackAt I e (g i) 0) lab' ∧ ∑ i, (lab' i).1 = ∑ i, (lab i).1 ∧
        IsPartialIso G₀ G₁ S'
  | 0, _, S, lab, hH, hPI => Forces.ret ⟨lab, hH, rfl, hPI⟩
  | n + 1, hn, S, lab, hH, hPI => by
    have h1 := sweep hk hg (σ := n) (by omega) false (hH.congr_cls fun i => by simp) hPI
    have hc : ∑ σ ∈ Finset.range (n + 1), (4 * k + 1) * hit e σ =
        (4 * k + 1) * hit e n + ∑ σ ∈ Finset.range n, (4 * k + 1) * hit e σ := by
      rw [Finset.sum_range_succ, Nat.add_comm]
    rw [hc]
    refine h1.bind fun S1 ⟨lab1, hH1, hs1, hPI1⟩ =>
      (strip_bwd hk hg n (by omega) S1 lab1 (hH1.congr_cls fun i => by simp) hPI1).weaken
        fun S2 ⟨lab2, hH2, hs2, hPI2⟩ => ⟨lab2, hH2, hs2.trans hs1, hPI2⟩

/-! ### The link -/

/-- From the last tracks through the links to the end coordinate classes. -/
lemma link_fwd (hg : Cols e g) {S : St I} {lab : Fin k → Lab}
    (hH : Holds S (fun i => trackAt I e (g i) (numSteps k ℓ)) lab)
    (hPI : IsPartialIso G₀ G₁ S) :
    Forces (2 * k + 2 * k) S fun S' => ∃ lab' : Fin k → Lab,
      Holds S' (fun i => endCls I e (g i)) lab' ∧ ∑ i, (lab' i).1 = ∑ i, (lab i).1 ∧
      IsPartialIso G₀ G₁ S' := by
  have hvL : ∀ i, ClsValid I (Cls.link e (g i) : ICls I) := fun i => hg.mem i
  refine (forces_replaceEvery hH hPI _ hvL (fun _ l l' => l'.1 = l.1)
    fun S1 i q hHi hs hPI1 => ?_).bind fun S1 ⟨lab1, hR1, hH1, hPI1⟩ => ?_
  · have := (forced_hub hPI1 hHi (hvL i) hs rfl).mp (by rw [hubB_link]; exact Or.inl ⟨rfl, rfl⟩)
    rw [hubB_link] at this
    rcases this with ⟨-, h⟩ | ⟨h, -⟩
    · exact h.symm
    · exact absurd h (trackAt_ne_endCls e (g i) _)
  · refine (forces_replaceEvery hH1 hPI1 _ (fun i => valid_endCls e (hg.mem i))
      (fun _ l l' => l'.1 = l.1) fun S2 i q hHi hs hPI2 => ?_).weaken
      fun S2 ⟨lab2, hR2, hH2, hPI2⟩ => ⟨lab2, hH2, ?_, hPI2⟩
    · have := (forced_nonhub hPI2 hHi (valid_endCls e (hg.mem i)) hs rfl).mp
        (by rw [hubB_link]; exact Or.inr ⟨rfl, rfl⟩)
      rw [hubB_link] at this
      rcases this with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h.symm (trackAt_ne_endCls e (g i) _)
      · exact h
    · exact Finset.sum_congr rfl fun i _ => (hR2 i).trans (hR1 i)

/-- From the end coordinate classes through the links to the last tracks. -/
lemma link_bwd (hg : Cols e g) {S : St I} {lab : Fin k → Lab}
    (hH : Holds S (fun i => endCls I e (g i)) lab) (hPI : IsPartialIso G₀ G₁ S) :
    Forces (2 * k + 2 * k) S fun S' => ∃ lab' : Fin k → Lab,
      Holds S' (fun i => trackAt I e (g i) (numSteps k ℓ)) lab' ∧
      ∑ i, (lab' i).1 = ∑ i, (lab i).1 ∧ IsPartialIso G₀ G₁ S' := by
  have hvL : ∀ i, ClsValid I (Cls.link e (g i) : ICls I) := fun i => hg.mem i
  refine (forces_replaceEvery hH hPI _ hvL (fun _ l l' => l'.1 = l.1)
    fun S1 i q hHi hs hPI1 => ?_).bind fun S1 ⟨lab1, hR1, hH1, hPI1⟩ => ?_
  · have := (forced_hub hPI1 hHi (hvL i) hs rfl).mp (by rw [hubB_link]; exact Or.inr ⟨rfl, rfl⟩)
    rw [hubB_link] at this
    rcases this with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h.symm (trackAt_ne_endCls e (g i) _)
    · exact h.symm
  · refine (forces_replaceEvery hH1 hPI1 _
      (fun i => valid_trackAt e (hg.mem i) le_rfl)
      (fun _ l l' => l'.1 = l.1) fun S2 i q hHi hs hPI2 => ?_).weaken
      fun S2 ⟨lab2, hR2, hH2, hPI2⟩ => ⟨lab2, hH2, ?_, hPI2⟩
    · have := (forced_nonhub hPI2 hHi (valid_trackAt e (hg.mem i) le_rfl) hs rfl).mp
        (by rw [hubB_link]; exact Or.inl ⟨rfl, rfl⟩)
      rw [hubB_link] at this
      rcases this with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h (trackAt_ne_endCls e (g i) _)
    · exact Finset.sum_congr rfl fun i _ => (hR2 i).trans (hR1 i)

/-! ### Junctions -/

/-- The neighbor classes of a junction. -/
def coordU (e : Fin I.schemas.length) (c : Coord k ℓ) : ICls I :=
  .coord (locU (sch I e)) ((permU (sch I e)).apply c)

/-- The neighbor classes of a junction. -/
def coordV (e : Fin I.schemas.length) (c : Coord k ℓ) : ICls I :=
  .coord (locV (sch I e)) ((permV (sch I e)).apply c)

lemma coordU_ne_coordV (ht : isTern (sch I e) = true) (c : Coord k ℓ) :
    coordU e c ≠ coordV e c := by
  simp only [coordU, coordV, ne_eq, Cls.coord.injEq, not_and]
  exact fun h => absurd h (locU_ne_locV e ht)

lemma hubB_junc' {c : Coord k ℓ} {l m : Lab} {Y : ICls I} :
    hubB I (.junc e c) l Y m = true ↔ (Y = coordU e c ∧ m.1 = l.1) ∨
      (Y = coordV e c ∧ m.1 = l.2) ∨ (Y = .sum e c ∧ m.1 = l.1 + l.2) :=
  hubB_junc

/-- A junction move: all representatives move between a junction class and one of its
neighbor classes. -/
lemma junc_move (ht : isTern (sch I e) = true) (hg : Cols e g) (toJunc : Bool)
    (nb : Fin k → ICls I) (hnb : ∀ i, nb i = coordU e (g i) ∨ nb i = coordV e (g i) ∨
      nb i = .sum e (g i))
    (hval : ∀ i, ClsValid I (nb i)) (f : Lab → ZMod 2)
    (hf : ∀ i l, (nb i = coordU e (g i) → f l = l.1) ∧ (nb i = coordV e (g i) → f l = l.2) ∧
      (nb i = .sum e (g i) → f l = l.1 + l.2))
    {S : St I} {lab : Fin k → Lab}
    (hH : Holds S (fun i => if toJunc then nb i else .junc e (g i)) lab)
    (hPI : IsPartialIso G₀ G₁ S) :
    Forces (2 * k) S fun S' => ∃ lab' : Fin k → Lab,
      (∀ i, if toJunc then f (lab' i) = (lab i).1 else (lab' i).1 = f (lab i)) ∧
      Holds S' (fun i => if toJunc then .junc e (g i) else nb i) lab' ∧
      IsPartialIso G₀ G₁ S' := by
  have hvJ : ∀ i, ClsValid I (Cls.junc e (g i) : ICls I) := fun i => ⟨ht, hg.mem i⟩
  have hvN : ∀ i, ClsValid I (if toJunc then Cls.junc e (g i) else nb i) := by
    intro i; split
    · exact hvJ i
    · exact hval i
  have hz : ∀ i, hubB I (.junc e (g i)) (0, 0) (nb i) (0, 0) = true := by
    intro i
    rw [hubB_junc']
    rcases hnb i with h | h | h
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr (Or.inl ⟨h, rfl⟩)
    · exact Or.inr (Or.inr ⟨h, by simp⟩)
  -- the label relation at a junction with label `l` and its neighbor with label `m`
  have hrel : ∀ i l m, hubB I (.junc e (g i)) l (nb i) m = true → m.1 = f l := by
    intro i l m h
    rw [hubB_junc'] at h
    have hU := (hf i l).1
    have hV := (hf i l).2.1
    have hS := (hf i l).2.2
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2, hU h1]
    · rw [h2, hV h1]
    · rw [h2, hS h1]
  refine (forces_replaceEvery hH hPI _ hvN
    (fun _ l l' => if toJunc then f l' = l.1 else l'.1 = f l) fun S1 i q hHi hs hPI1 => ?_).weaken
    fun S' ⟨lab', h1, h2, h3⟩ => ⟨lab', h1, h2, h3⟩
  cases toJunc
  · simp only [Bool.false_eq_true, if_false] at hHi hs ⊢
    exact hrel i _ _ ((forced_nonhub hPI1 hHi (hval i) hs rfl).mp (hz i))
  · simp only [if_true] at hHi hs ⊢
    exact (hrel i _ _ ((forced_hub hPI1 hHi (hvJ i) hs rfl).mp (hz i))).symm

end Lax119563Proofs.Matrix
