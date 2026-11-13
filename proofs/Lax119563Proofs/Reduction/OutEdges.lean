import Lax119563Proofs.Reduction.OutCorr
import Lax119563Proofs.Matrix.SpoilerStrip
import Lax119563Proofs.Matrix.Edges

/-!
# Neighbors of hubs in the output graphs

Every edge of `G_ε` joins a hub with a non-hub. `hubNbrs I ε a` lists the valid neighbors of
a hub name `a` in the order of the output (`nbrCand`): for `upd` the incoming track, the
outgoing track, the coefficient; for `junc` the two argument coordinates and the sum; for
`link` the end coordinate and the last track. `adjN_iff_hubNbrs`: valid names are adjacent
iff one is a hub and the other is among its `hubNbrs`.
-/

open Lax119563.ColoredGraphs Lax119563.ImplicitParitySystems Lax119563Proofs.Matrix

namespace Lax119563Proofs.Reduction

variable {s ℓ : ℕ} (I : ImplicitParitySystem (s + 1) ℓ)

/-- The neighbor classes of a hub with the effective first label bits prescribed by `hubB`,
in output order. -/
def nbrCand : ICls I → Lab → List (ICls I × ZMod 2)
  | .upd e σ c, l => [(trackAt I e c σ, l.1), (.track e σ c, l.2), (.coef e σ, l.1 + l.2)]
  | .junc e c, l => [(.coord (locU (sch I e)) ((permU (sch I e)).apply c), l.1),
      (.coord (locV (sch I e)) ((permV (sch I e)).apply c), l.2), (.sum e c, l.1 + l.2)]
  | .link e c, l => [(endCls I e c, l.1), (trackAt I e c (numSteps (s + 1) ℓ), l.1)]
  | _, _ => []

/-- The name of class `Y` with effective first label bit `r` in `G_ε`. -/
def nameOfEff (ε : ZMod 2) (Y : ICls I) (r : ZMod 2) : VName I := (Y, (r - ε * initBit I Y, 0))

open Classical in
/-- The valid neighbors of a hub name. -/
noncomputable def hubNbrs (ε : ZMod 2) (a : VName I) : List (VName I) :=
  ((nbrCand I a.1 a.2).map fun p => nameOfEff I ε p.1 p.2).filter fun b => Valid I b

lemma isHub_of_mem_nbrCand {X : ICls I} {l : Lab} {p : ICls I × ZMod 2}
    (h : p ∈ nbrCand I X l) : isHub I X = true ∧ isHub I p.1 = false := by
  cases X <;> simp only [nbrCand, List.mem_cons, List.not_mem_nil, or_false] at h <;>
    (try rcases h with rfl | rfl | rfl) <;> (try rcases h with rfl | rfl) <;>
    refine ⟨rfl, ?_⟩ <;>
    first | exact isHub_trackAt I _ _ _ | exact isHub_endCls I _ _ | rfl

lemma mem_hubNbrs_nonhub {ε : ZMod 2} {a b : VName I} (h : b ∈ hubNbrs I ε a) :
    isHub I a.1 = true ∧ isHub I b.1 = false := by
  unfold hubNbrs at h
  obtain ⟨hb, -⟩ := List.mem_filter.mp h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
  exact isHub_of_mem_nbrCand I hp

lemma initBit_hub {X : ICls I} (h : isHub I X = true) : initBit I X = 0 := by
  cases X <;> simp_all [isHub, initBit]

lemma eff_hub (ε : ZMod 2) {a : VName I} (h : isHub I a.1 = true) : eff I ε a = a.2 := by
  simp [eff, initBit_hub I h]

/-- A valid non-hub name is the name of its class with its effective label. -/
lemma eq_nameOfEff (ε : ZMod 2) {b : VName I} (hb : Valid I b) (hh : isHub I b.1 = false) :
    b = nameOfEff I ε b.1 (eff I ε b).1 := by
  obtain ⟨Y, m⟩ := b
  have h2 : m.2 = 0 := hb.2.1 (twoBit_of_not_hub hh)
  simp only [nameOfEff, eff, add_sub_cancel_right]
  ext <;> simp [h2]

lemma eff_nameOfEff (ε : ZMod 2) (Y : ICls I) (r : ZMod 2) :
    (eff I ε (nameOfEff I ε Y r)).1 = r := by
  simp [eff, nameOfEff]

/-- Adjacency of a valid hub name. -/
lemma adjN_hub_iff (ε : ZMod 2) {a b : VName I} (ha : isHub I a.1 = true) (hb : Valid I b) :
    adjN I ε a b ↔ b ∈ hubNbrs I ε a := by
  have hrev : ¬ hubB I b.1 (eff I ε b) a.1 (eff I ε a) = true := fun h => by
    have := (hubB_hub I h).2; rw [ha] at this; cases this
  unfold adjN
  rw [or_iff_left hrev, eff_hub I ε ha]
  unfold hubNbrs
  rw [List.mem_filter, List.mem_map]
  simp only [hb, decide_true, and_true]
  constructor
  · intro h
    have hbh := (hubB_hub I h).2
    refine ⟨(b.1, (eff I ε b).1), ?_, (eq_nameOfEff I ε hb hbh).symm⟩
    obtain ⟨X, l⟩ := a
    cases X with
    | upd e σ c =>
      rw [hubB_upd] at h
      simp only [nbrCand, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · exact Or.inr (Or.inr ⟨h1, h2⟩)
    | junc e c =>
      rw [hubB_junc] at h
      simp only [nbrCand, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · exact Or.inr (Or.inr ⟨h1, h2⟩)
    | link e c =>
      rw [hubB_link] at h
      simp only [nbrCand, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
    | _ => simp [isHub] at ha
  · rintro ⟨⟨Y, r⟩, hp, rfl⟩
    have hr := eff_nameOfEff I ε Y r
    obtain ⟨X, l⟩ := a
    cases X with
    | upd e σ c =>
      rw [hubB_upd]
      simp only [nbrCand, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, hr⟩
      · exact Or.inr (Or.inl ⟨rfl, hr⟩)
      · exact Or.inr (Or.inr ⟨rfl, hr⟩)
    | junc e c =>
      rw [hubB_junc]
      simp only [nbrCand, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, hr⟩
      · exact Or.inr (Or.inl ⟨rfl, hr⟩)
      · exact Or.inr (Or.inr ⟨rfl, hr⟩)
    | link e c =>
      rw [hubB_link]
      simp only [nbrCand, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, hr⟩
      · exact Or.inl ⟨rfl, hr⟩
    | _ => simp [isHub] at ha

/-- **Adjacency in terms of hub neighbors.** -/
lemma adjN_iff_hubNbrs (ε : ZMod 2) {a b : VName I} (ha : Valid I a) (hb : Valid I b) :
    adjN I ε a b ↔ (isHub I a.1 = true ∧ b ∈ hubNbrs I ε a) ∨
      (isHub I b.1 = true ∧ a ∈ hubNbrs I ε b) := by
  constructor
  · intro h
    by_cases hah : isHub I a.1 = true
    · exact Or.inl ⟨hah, (adjN_hub_iff I ε hah hb).mp h⟩
    · by_cases hbh : isHub I b.1 = true
      · exact Or.inr ⟨hbh, (adjN_hub_iff I ε hbh ha).mp (adjN_symm I ε a b h)⟩
      · exfalso
        rcases h with h | h
        · exact hah (hubB_hub I h).1
        · exact hbh (hubB_hub I h).1
  · rintro (⟨hah, h⟩ | ⟨hbh, h⟩)
    · exact (adjN_hub_iff I ε hah hb).mpr h
    · exact adjN_symm I ε b a ((adjN_hub_iff I ε hbh ha).mpr h)

end Lax119563Proofs.Reduction
