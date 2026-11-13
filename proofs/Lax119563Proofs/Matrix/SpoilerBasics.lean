import Lax119563Proofs.Matrix.Duplicator

/-!
# Spoiler's moves

Spoiler always places pebbles on zero vertices of `G₀` (label `(0, 0)`). Pebbles
`0, …, k - 1` hold *representatives*; pebble `k` is the spare. Replacing a representative
costs two rounds: the spare is placed on the new vertex, then the representative is moved
onto the same vertex, where Duplicator has to answer with the same image.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems
open Lax119563.ColoredGraphs Lax119563.PebbleGame

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

local notation "G₀" => matrixGraph I 0
local notation "G₁" => matrixGraph I 1

/-- Game states of the `(k + 1)`-pebble game on the matrix graphs. -/
abbrev St (I : ImplicitParitySystem k ℓ) := GameState (k + 1) (matrixGraph I 0) (matrixGraph I 1)

/-- The spare pebble. -/
abbrev spare : Fin (k + 1) := Fin.last k

lemma valid_zero {X : ICls I} (hX : ClsValid I X) : Valid I (X, ((0 : ZMod 2), (0 : ZMod 2))) :=
  ⟨hX, fun _ => rfl, fun _ => rfl⟩

/-- The zero vertex of a class. -/
def zv (X : ICls I) (hX : ClsValid I X) : Fin (nV I) :=
  idx (X, (0, 0)) ((mem_vertexList I _).mpr (valid_zero hX))

@[simp] lemma nm_zv (X : ICls I) (hX : ClsValid I X) : nm (zv X hX) = (X, (0, 0)) := nm_idx _ _

lemma eff_zero (X : ICls I) : eff I 0 (X, ((0 : ZMod 2), (0 : ZMod 2))) = (0, 0) := by
  simp [eff]

/-- Pebble `j` holds the zero vertex of class `X`, matched with a vertex of `G₁` of effective
label `l`. -/
def HoldsAt (S : St I) (j : Fin (k + 1)) (X : ICls I) (l : Lab) : Prop :=
  ∃ p q, S j = some (p, q) ∧ nm p = (X, (0, 0)) ∧ (nm q).1 = X ∧ eff I 1 (nm q) = l

/-- The representatives hold the classes `cls` with labels `lab`. -/
def Holds (S : St I) (cls : Fin k → ICls I) (lab : Fin k → Lab) : Prop :=
  ∀ i, HoldsAt S i.castSucc (cls i) (lab i)

lemma castSucc_ne_spare (i : Fin k) : (i.castSucc : Fin (k + 1)) ≠ spare :=
  Fin.castSucc_ne_last i

lemma HoldsAt.update_ne {S : St I} {j j' : Fin (k + 1)} {X : ICls I} {l : Lab}
    (h : HoldsAt S j X l) (hj : j ≠ j') (v : Option (Fin (nV I) × Fin (nV I))) :
    HoldsAt (Function.update S j' v) j X l := by
  obtain ⟨p, q, h1, h2⟩ := h
  exact ⟨p, q, by rw [Function.update_of_ne hj]; exact h1, h2⟩

lemma Holds.update_spare {S : St I} {cls : Fin k → ICls I} {lab : Fin k → Lab}
    (h : Holds S cls lab) (v : Option (Fin (nV I) × Fin (nV I))) :
    Holds (Function.update S spare v) cls lab :=
  fun i => (h i).update_ne (castSucc_ne_spare i) v

/-! ### Partial isomorphisms -/

lemma pi_adj {S : St I} (hPI : IsPartialIso G₀ G₁ S) {j j' : Fin (k + 1)} {p q p' q' : Fin (nV I)}
    (hj : S j = some (p, q)) (hj' : S j' = some (p', q')) :
    adjN I 0 (nm p) (nm p') ↔ adjN I 1 (nm q) (nm q') :=
  (hPI j j' p q p' q' hj hj').2.1

lemma pi_cls {S : St I} (hPI : IsPartialIso G₀ G₁ S) {j : Fin (k + 1)} {p q : Fin (nV I)}
    (hj : S j = some (p, q)) : (nm q).1 = (nm p).1 :=
  ((matrixGraph_color 0 1 p q).mp (hPI j j p q p q hj hj).2.2).symm

lemma pi_eq {S : St I} (hPI : IsPartialIso G₀ G₁ S) {j j' : Fin (k + 1)} {p q q' : Fin (nV I)}
    (hj : S j = some (p, q)) (hj' : S j' = some (p, q')) : q = q' :=
  (hPI j j' p q p q' hj hj').1.mp rfl

lemma adjN_iff_hub (ε : ZMod 2) {x y : VName I} (hx : isHub I x.1 = true) :
    adjN I ε x y ↔ hubB I x.1 (eff I ε x) y.1 (eff I ε y) = true := by
  unfold adjN
  constructor
  · rintro (h | h)
    · exact h
    · have := (hubB_hub I h).2
      rw [hx] at this
      exact absurd this (by decide)
  · exact Or.inl

/-- What Duplicator's answer `q` on the spare reveals about a representative, for a hub class
`Y` placed next to a held class `X`. -/
lemma forced_hub {S : St I} (hPI : IsPartialIso G₀ G₁ S) {j : Fin (k + 1)} {X : ICls I} {l : Lab}
    (hj : HoldsAt S j X l) {Y : ICls I} (hY : ClsValid I Y) {q : Fin (nV I)}
    (hs : S spare = some (zv Y hY, q)) (hYhub : isHub I Y = true) :
    hubB I Y (0, 0) X (0, 0) = true ↔ hubB I Y (eff I 1 (nm q)) X l = true := by
  obtain ⟨p, q', h1, h2, h3, h4⟩ := hj
  have := pi_adj hPI hs h1
  have hq : (nm q).1 = Y := by rw [pi_cls hPI hs, nm_zv]
  rw [nm_zv, h2, adjN_iff_hub 0 hYhub, adjN_iff_hub 1 (by rw [hq]; exact hYhub), eff_zero,
    eff_zero, h4, hq, h3] at this
  exact this

/-- The same, for a hub `X` held by a representative and a non-hub class `Y` on the spare. -/
lemma forced_nonhub {S : St I} (hPI : IsPartialIso G₀ G₁ S) {j : Fin (k + 1)} {X : ICls I}
    {l : Lab} (hj : HoldsAt S j X l) {Y : ICls I} (hY : ClsValid I Y) {q : Fin (nV I)}
    (hs : S spare = some (zv Y hY, q)) (hXhub : isHub I X = true) :
    hubB I X (0, 0) Y (0, 0) = true ↔ hubB I X l Y (eff I 1 (nm q)) = true := by
  obtain ⟨p, q', h1, h2, h3, h4⟩ := hj
  have := pi_adj hPI h1 hs
  have hq : (nm q).1 = Y := by rw [pi_cls hPI hs, nm_zv]
  rw [nm_zv, h2, adjN_iff_hub 0 hXhub, adjN_iff_hub 1 (by rw [h3]; exact hXhub), eff_zero,
    eff_zero, h4, hq, h3] at this
  exact this

lemma spare_cls {S : St I} (hPI : IsPartialIso G₀ G₁ S) {Y : ICls I} (hY : ClsValid I Y)
    {q : Fin (nV I)} (hs : S spare = some (zv Y hY, q)) : (nm q).1 = Y := by
  rw [pi_cls hPI hs, nm_zv]

/-! ### Moves -/

/-- Placing the spare on the zero vertex of `Y`. -/
lemma forces_spare (S : St I) (Y : ICls I) (hY : ClsValid I Y) :
    Forces 1 S fun S' => ∃ q, S' = Function.update S spare (some (zv Y hY, q)) ∧
      IsPartialIso G₀ G₁ S' :=
  Forces.place S spare (zv Y hY)

/-- Replacing representative `i` by the zero vertex of `Y`. -/
lemma forces_replace (S : St I) (i : Fin k) (Y : ICls I) (hY : ClsValid I Y) :
    Forces 2 S fun S' => ∃ q, IsPartialIso G₀ G₁ (Function.update S spare (some (zv Y hY, q))) ∧
      S' = Function.update (Function.update S spare (some (zv Y hY, q))) i.castSucc
        (some (zv Y hY, q)) ∧ IsPartialIso G₀ G₁ S' := by
  refine Forces.mono (le_refl (1 + 1)) ((forces_spare S Y hY).bind fun S1 ⟨q, hS1, hPI1⟩ => ?_)
  refine (Forces.place S1 i.castSucc (zv Y hY)).weaken fun S2 ⟨q2, hS2, hPI2⟩ => ?_
  have hq : q2 = q := by
    refine pi_eq hPI2 (p := zv Y hY) (j := i.castSucc) (j' := spare) ?_ ?_
    · rw [hS2]; simp
    · rw [hS2, Function.update_of_ne (castSucc_ne_spare i).symm, hS1]; simp
  subst hq hS1
  exact ⟨q2, hPI1, hS2, hPI2⟩

/-- Replacing representative `i` by class `Y`, where the answer satisfies `R`. -/
lemma forces_step {S : St I} {cls : Fin k → ICls I} {lab : Fin k → Lab} (hH : Holds S cls lab)
    (i : Fin k) (Y : ICls I) (hY : ClsValid I Y) (R : Lab → Prop)
    (hR : ∀ q, IsPartialIso G₀ G₁ (Function.update S spare (some (zv Y hY, q))) →
      R (eff I 1 (nm q))) :
    Forces 2 S fun S' => ∃ l, R l ∧ Holds S' (Function.update cls i Y)
      (Function.update lab i l) ∧ IsPartialIso G₀ G₁ S' := by
  refine (forces_replace S i Y hY).weaken fun S' ⟨q, hPI1, hS', hPI'⟩ => ?_
  refine ⟨eff I 1 (nm q), hR q hPI1, fun j => ?_, hPI'⟩
  by_cases hji : j = i
  · subst hji
    refine ⟨zv Y hY, q, by rw [hS']; simp, by simp, ?_, by simp⟩
    rw [Function.update_self]
    exact spare_cls (hY := hY) hPI1 (Function.update_self _ _ _)
  · rw [Function.update_of_ne hji, Function.update_of_ne hji, hS']
    exact ((hH j).update_ne (castSucc_ne_spare j) _).update_ne
      (fun h => hji (Fin.castSucc_injective _ h)) _

/-- Replacing the representatives in the list `T` one after the other. -/
lemma forces_replaceAll (T : List (Fin k)) (hT : T.Nodup) {S : St I} {cls : Fin k → ICls I}
    {lab : Fin k → Lab} (hH : Holds S cls lab) (hPI : IsPartialIso G₀ G₁ S) (newCls : Fin k → ICls I)
    (hval : ∀ i ∈ T, ClsValid I (newCls i)) (R : Fin k → Lab → Lab → Prop)
    (hR : ∀ (S1 : St I) i q (hi : i ∈ T), HoldsAt S1 i.castSucc (cls i) (lab i) →
      S1 spare = some (zv (newCls i) (hval i hi), q) → IsPartialIso G₀ G₁ S1 →
      R i (lab i) (eff I 1 (nm q))) :
    Forces (2 * T.length) S fun S' => ∃ lab' : Fin k → Lab,
      (∀ i ∈ T, R i (lab i) (lab' i)) ∧ (∀ i, i ∉ T → lab' i = lab i) ∧
      Holds S' (fun i => if i ∈ T then newCls i else cls i) lab' ∧ IsPartialIso G₀ G₁ S' := by
  induction T generalizing S cls lab with
  | nil =>
    refine Forces.ret ⟨lab, by simp, fun _ _ => rfl, by simpa using hH, hPI⟩
  | cons i T ih =>
    obtain ⟨hiT, hT'⟩ := List.nodup_cons.mp hT
    have hstep := forces_step hH i (newCls i) (hval i List.mem_cons_self) (R i (lab i))
      fun q hPI => hR _ i q List.mem_cons_self ((hH i).update_ne (castSucc_ne_spare i) _)
        (Function.update_self ..) hPI
    refine Forces.mono (show 2 + 2 * T.length ≤ 2 * (i :: T).length by simp; omega)
      (hstep.bind fun S1 ⟨l, hl, hH1, hPI1⟩ => ?_)
    refine (ih hT' hH1 hPI1 (fun j hj => hval j (List.mem_cons_of_mem _ hj))
      fun S2 j q hj hj2 hs hPI2 => ?_).weaken
      fun S' ⟨lab', h1, h2, h3, h4⟩ => ?_
    · have hji : j ≠ i := fun h => hiT (h ▸ hj)
      rw [Function.update_of_ne hji] at hj2 ⊢
      rw [Function.update_of_ne hji] at hj2
      exact hR S2 j q (List.mem_cons_of_mem _ hj) hj2 hs hPI2
    · refine ⟨lab', fun j hj => ?_, fun j hj => ?_, ?_, h4⟩
      · rcases List.mem_cons.mp hj with rfl | hj
        · rw [h2 j hiT]; simpa using hl
        · have hji : j ≠ i := fun h => hiT (h ▸ hj)
          have := h1 j hj
          rwa [Function.update_of_ne hji] at this
      · have hji : j ≠ i := fun h => hj (h ▸ List.mem_cons_self)
        rw [h2 j fun h => hj (List.mem_cons_of_mem _ h), Function.update_of_ne hji]
      · convert h3 using 2 with j
        by_cases hji : j = i
        · subst hji; simp [hiT]
        · simp [hji]

end Lax119563Proofs.Matrix
