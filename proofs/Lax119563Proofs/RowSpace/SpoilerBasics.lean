import Lax119563Proofs.RowSpace.Extension
import Lax119563Proofs.Matrix.SpoilerMain

/-!
# Spoiler's moves on the row-space graphs

Spoiler always places pebbles on zero vertices `(X, 0)` of `G₀`. Pebbles `0, …, k - 1` hold
*representatives*; pebble `k` is the spare. Replacing a representative costs two rounds: the
spare is placed on the new vertex, then the representative is moved onto the same vertex,
where Duplicator has to answer with the same image.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems
open Lax119563.ColoredGraphs Lax119563.PebbleGame
open Lax119563Proofs.Matrix

namespace Lax119563Proofs.RowSpace

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

local notation "G₀" => rsGraph I 0
local notation "G₁" => rsGraph I 1

/-- Game states of the `(k + 1)`-pebble game on the row-space graphs. -/
abbrev RSt (I : ImplicitParitySystem k ℓ) := GameState (k + 1) (rsGraph I 0) (rsGraph I 1)

/-! ### Zero vertices -/

lemma zero_mem_labs {X : ICls I} (hX : X ∈ classes I) : (0 : RLab k ℓ) ∈ labs I X := by
  cases X with
  | coord v c => simp only [labs]; split <;> simp [lab1]
  | sum => simp [labs, lab1]
  | junc => simp [labs, lab2]
  | link => exact absurd hX link_not_mem
  | track => simp [labs, lab1]
  | upd => simp [labs, lab2]
  | coef e h =>
    simp only [labs, Finset.mem_image]
    exact ⟨0, zero_mem_maskSet I e, rfl⟩

lemma zero_mem_verts {X : ICls I} (hX : X ∈ classes I) : (X, (0 : RLab k ℓ)) ∈ verts I 0 := by
  rw [verts_zero, mem_names]
  exact ⟨hX, zero_mem_labs hX⟩

/-- The zero vertex of a class in `G₀`. -/
noncomputable def rzv (X : ICls I) (hX : X ∈ classes I) : Fin (rsGraph I 0).n :=
  ix 0 (X, 0) (zero_mem_verts hX)

@[simp] lemma vx_rzv (X : ICls I) (hX : X ∈ classes I) : vx (rzv X hX) = (X, 0) := vx_ix _ _

/-- Pebble `j` holds the zero vertex of class `X`, matched with the vertex `(X, l)` of `G₁`. -/
def RHoldsAt (S : RSt I) (j : Fin (k + 1)) (X : ICls I) (l : RLab k ℓ) : Prop :=
  ∃ p q, S j = some (p, q) ∧ vx p = (X, 0) ∧ vx q = (X, l)

/-- The representatives hold the classes `cls` with labels `lab`. -/
def RHolds (S : RSt I) (cls : Fin k → ICls I) (lab : Fin k → RLab k ℓ) : Prop :=
  ∀ i, RHoldsAt S i.castSucc (cls i) (lab i)

lemma RHoldsAt.update_ne {S : RSt I} {j j' : Fin (k + 1)} {X : ICls I} {l : RLab k ℓ}
    (h : RHoldsAt S j X l) (hj : j ≠ j') (v : Option (Fin (rsGraph I 0).n × Fin (rsGraph I 1).n)) :
    RHoldsAt (Function.update S j' v) j X l := by
  obtain ⟨p, q, h1, h2⟩ := h
  exact ⟨p, q, by rw [Function.update_of_ne hj]; exact h1, h2⟩

lemma RHolds.update_spare {S : RSt I} {cls : Fin k → ICls I} {lab : Fin k → RLab k ℓ}
    (h : RHolds S cls lab) (v : Option (Fin (rsGraph I 0).n × Fin (rsGraph I 1).n)) :
    RHolds (Function.update S spare v) cls lab :=
  fun i => (h i).update_ne (castSucc_ne_spare i) v

lemma RHolds.congr_cls {S : RSt I} {cls cls' : Fin k → ICls I} {lab : Fin k → RLab k ℓ}
    (h : RHolds S cls lab) (hc : ∀ i, cls i = cls' i) : RHolds S cls' lab := by
  rwa [show cls = cls' from funext hc] at h

/-! ### Partial isomorphisms -/

lemma rpi_adj {S : RSt I} (hPI : IsPartialIso G₀ G₁ S) {j j' : Fin (k + 1)}
    {p p' : Fin (rsGraph I 0).n} {q q' : Fin (rsGraph I 1).n}
    (hj : S j = some (p, q)) (hj' : S j' = some (p', q')) :
    radj I (vx p) (vx p') ↔ radj I (vx q) (vx q') :=
  (hPI j j' p q p' q' hj hj').2.1

lemma rpi_cls {S : RSt I} (hPI : IsPartialIso G₀ G₁ S) {j : Fin (k + 1)}
    {p : Fin (rsGraph I 0).n} {q : Fin (rsGraph I 1).n}
    (hj : S j = some (p, q)) : (vx q).1 = (vx p).1 :=
  ((rs_color_eq p q).mp (hPI j j p q p q hj hj).2.2).symm

lemma rpi_eq {S : RSt I} (hPI : IsPartialIso G₀ G₁ S) {j j' : Fin (k + 1)}
    {p : Fin (rsGraph I 0).n} {q q' : Fin (rsGraph I 1).n}
    (hj : S j = some (p, q)) (hj' : S j' = some (p, q')) : q = q' :=
  (hPI j j' p q p q' hj hj').1.mp rfl

lemma rspare_vx {S : RSt I} (hPI : IsPartialIso G₀ G₁ S) {Y : ICls I} (hY : Y ∈ classes I)
    {q : Fin (rsGraph I 1).n} (hs : S spare = some (rzv Y hY, q)) : vx q = (Y, (vx q).2) := by
  have h := rpi_cls hPI hs
  rw [vx_rzv] at h
  exact Prod.ext h rfl

/-- What Duplicator's answer `q` on the spare reveals, for a hub class `Y` placed next to a
held class `X`. -/
lemma rforced_hub {S : RSt I} (hPI : IsPartialIso G₀ G₁ S) {j : Fin (k + 1)} {X : ICls I}
    {l : RLab k ℓ} (hj : RHoldsAt S j X l) {Y : ICls I} (hY : Y ∈ classes I)
    {q : Fin (rsGraph I 1).n} (hs : S spare = some (rzv Y hY, q)) (hYhub : isHubR I Y) :
    hubR I Y 0 X 0 ↔ hubR I Y (vx q).2 X l := by
  obtain ⟨p, q', h1, h2, h3⟩ := hj
  have := rpi_adj hPI hs h1
  rw [vx_rzv, h2, h3, rspare_vx hPI hY hs, radj_iff_hub I hYhub, radj_iff_hub I hYhub] at this
  exact this

/-- The same, for a hub `X` held by a representative and a non-hub class `Y` on the spare. -/
lemma rforced_nonhub {S : RSt I} (hPI : IsPartialIso G₀ G₁ S) {j : Fin (k + 1)} {X : ICls I}
    {l : RLab k ℓ} (hj : RHoldsAt S j X l) {Y : ICls I} (hY : Y ∈ classes I)
    {q : Fin (rsGraph I 1).n} (hs : S spare = some (rzv Y hY, q)) (hXhub : isHubR I X) :
    hubR I X 0 Y 0 ↔ hubR I X l Y (vx q).2 := by
  obtain ⟨p, q', h1, h2, h3⟩ := hj
  have := rpi_adj hPI h1 hs
  rw [vx_rzv, h2, h3, rspare_vx hPI hY hs, radj_iff_hub I hXhub, radj_iff_hub I hXhub] at this
  exact this

/-! ### Moves -/

/-- Placing the spare on the zero vertex of `Y`. -/
lemma rforces_spare (S : RSt I) (Y : ICls I) (hY : Y ∈ classes I) :
    Forces 1 S fun S' => ∃ q, S' = Function.update S spare (some (rzv Y hY, q)) ∧
      IsPartialIso G₀ G₁ S' :=
  Forces.place S spare (rzv Y hY)

/-- Replacing representative `i` by the zero vertex of `Y`. -/
lemma rforces_replace (S : RSt I) (i : Fin k) (Y : ICls I) (hY : Y ∈ classes I) :
    Forces 2 S fun S' => ∃ q, IsPartialIso G₀ G₁ (Function.update S spare (some (rzv Y hY, q))) ∧
      S' = Function.update (Function.update S spare (some (rzv Y hY, q))) i.castSucc
        (some (rzv Y hY, q)) ∧ IsPartialIso G₀ G₁ S' := by
  refine Forces.mono (le_refl (1 + 1)) ((rforces_spare S Y hY).bind fun S1 ⟨q, hS1, hPI1⟩ => ?_)
  refine (Forces.place S1 i.castSucc (rzv Y hY)).weaken fun S2 ⟨q2, hS2, hPI2⟩ => ?_
  have hq : q2 = q := by
    refine rpi_eq hPI2 (p := rzv Y hY) (j := i.castSucc) (j' := spare) ?_ ?_
    · rw [hS2]; simp
    · rw [hS2, Function.update_of_ne (castSucc_ne_spare i).symm, hS1]; simp
  subst hq hS1
  exact ⟨q2, hPI1, hS2, hPI2⟩

/-- Replacing representative `i` by class `Y`, where the answer satisfies `R`. -/
lemma rforces_step {S : RSt I} {cls : Fin k → ICls I} {lab : Fin k → RLab k ℓ}
    (hH : RHolds S cls lab) (i : Fin k) (Y : ICls I) (hY : Y ∈ classes I) (R : RLab k ℓ → Prop)
    (hR : ∀ q, IsPartialIso G₀ G₁ (Function.update S spare (some (rzv Y hY, q))) →
      R (vx q).2) :
    Forces 2 S fun S' => ∃ l, R l ∧ RHolds S' (Function.update cls i Y)
      (Function.update lab i l) ∧ IsPartialIso G₀ G₁ S' := by
  refine (rforces_replace S i Y hY).weaken fun S' ⟨q, hPI1, hS', hPI'⟩ => ?_
  refine ⟨(vx q).2, hR q hPI1, fun j => ?_, hPI'⟩
  by_cases hji : j = i
  · subst hji
    refine ⟨rzv Y hY, q, by rw [hS']; simp, by simp, ?_⟩
    rw [Function.update_self, Function.update_self]
    exact rspare_vx hPI1 hY (Function.update_self _ _ _)
  · rw [Function.update_of_ne hji, Function.update_of_ne hji, hS']
    exact ((hH j).update_ne (castSucc_ne_spare j) _).update_ne
      (fun h => hji (Fin.castSucc_injective _ h)) _

/-- Replacing the representatives in the list `T` one after the other. -/
lemma rforces_replaceAll (T : List (Fin k)) (hT : T.Nodup) {S : RSt I} {cls : Fin k → ICls I}
    {lab : Fin k → RLab k ℓ} (hH : RHolds S cls lab) (hPI : IsPartialIso G₀ G₁ S)
    (newCls : Fin k → ICls I) (hval : ∀ i ∈ T, newCls i ∈ classes I)
    (R : Fin k → RLab k ℓ → RLab k ℓ → Prop)
    (hR : ∀ (S1 : RSt I) i q (hi : i ∈ T), RHoldsAt S1 i.castSucc (cls i) (lab i) →
      S1 spare = some (rzv (newCls i) (hval i hi), q) → IsPartialIso G₀ G₁ S1 →
      R i (lab i) (vx q).2) :
    Forces (2 * T.length) S fun S' => ∃ lab' : Fin k → RLab k ℓ,
      (∀ i ∈ T, R i (lab i) (lab' i)) ∧ (∀ i, i ∉ T → lab' i = lab i) ∧
      RHolds S' (fun i => if i ∈ T then newCls i else cls i) lab' ∧ IsPartialIso G₀ G₁ S' := by
  induction T generalizing S cls lab with
  | nil =>
    refine Forces.ret ⟨lab, by simp, fun _ _ => rfl, by simpa using hH, hPI⟩
  | cons i T ih =>
    obtain ⟨hiT, hT'⟩ := List.nodup_cons.mp hT
    have hstep := rforces_step hH i (newCls i) (hval i List.mem_cons_self) (R i (lab i))
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

/-- Replacing every representative. -/
lemma rforces_replaceEvery {S : RSt I} {cls : Fin k → ICls I} {lab : Fin k → RLab k ℓ}
    (hH : RHolds S cls lab) (hPI : IsPartialIso G₀ G₁ S) (newCls : Fin k → ICls I)
    (hval : ∀ i, newCls i ∈ classes I) (R : Fin k → RLab k ℓ → RLab k ℓ → Prop)
    (hR : ∀ (S1 : RSt I) i q, RHoldsAt S1 i.castSucc (cls i) (lab i) →
      S1 spare = some (rzv (newCls i) (hval i), q) → IsPartialIso G₀ G₁ S1 →
      R i (lab i) (vx q).2) :
    Forces (2 * k) S fun S' => ∃ lab' : Fin k → RLab k ℓ, (∀ i, R i (lab i) (lab' i)) ∧
      RHolds S' newCls lab' ∧ IsPartialIso G₀ G₁ S' := by
  have := rforces_replaceAll (List.finRange k) (List.nodup_finRange k) hH hPI newCls
    (fun i _ => hval i) R fun S1 i q _ h1 h2 h3 => hR S1 i q h1 h2 h3
  rw [List.length_finRange] at this
  exact this.weaken fun S' ⟨lab', h1, _, h3, h4⟩ =>
    ⟨lab', fun i => h1 i (List.mem_finRange i), h3.congr_cls fun i => by simp, h4⟩

/-- Placing the representatives on the zero vertices of the classes `cls`. -/
lemma rforces_fill (T : List (Fin k)) (hT : T.Nodup) {S : RSt I} (hPI : IsPartialIso G₀ G₁ S)
    (cls : Fin k → ICls I) (hval : ∀ i, cls i ∈ classes I) :
    Forces (2 * T.length) S fun S' => (∀ i ∈ T, ∃ l, RHoldsAt S' i.castSucc (cls i) l) ∧
      (∀ i, i ∉ T → S' i.castSucc = S i.castSucc) ∧ IsPartialIso G₀ G₁ S' := by
  induction T generalizing S with
  | nil => exact Forces.ret ⟨by simp, fun _ _ => rfl, hPI⟩
  | cons i T ih =>
    obtain ⟨hiT, hT'⟩ := List.nodup_cons.mp hT
    refine Forces.mono (show 2 + 2 * T.length ≤ 2 * (i :: T).length by simp; omega)
      ((rforces_replace S i (cls i) (hval i)).bind fun S1 ⟨q, hPI1, hS1, hPI1'⟩ =>
        (ih hT' hPI1').weaken fun S' ⟨h1, h2, h3⟩ => ⟨fun j hj => ?_, fun j hj => ?_, h3⟩)
    · rcases List.mem_cons.mp hj with rfl | hj
      · refine ⟨(vx q).2, rzv (cls j) (hval j), q, ?_, by simp, ?_⟩
        · rw [h2 j hiT, hS1]; simp
        · exact rspare_vx hPI1 (hval j) (Function.update_self ..)
      · exact h1 j hj
    · have hji : j ≠ i := fun h => hj (h ▸ List.mem_cons_self)
      rw [h2 j fun h => hj (List.mem_cons_of_mem _ h), hS1,
        Function.update_of_ne (fun h => hji (Fin.castSucc_injective _ h)),
        Function.update_of_ne (castSucc_ne_spare j)]

end Lax119563Proofs.RowSpace
