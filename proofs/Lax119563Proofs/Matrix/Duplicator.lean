import Lax119563Proofs.Matrix.Extension
import Lax119563Proofs.Matrix.GameLemmas

/-!
# Duplicator's strategy

Duplicator survives `r` rounds of the bijective `(k + 1)`-pebble game on
`(matrixGraph I 0, matrixGraph I 1)` whenever `K_r` is conflict-free (Theorem
"Matrix compiler", part (II)).
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems
open Lax119563.ColoredGraphs Lax119563.PebbleGame

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-! ### Vertices and names -/

/-- The number of vertices of both graphs. -/
abbrev nV : ℕ := (vertexList I).length

variable {I}

/-- The name of a vertex. -/
def nm (i : Fin (nV I)) : VName I := (vertexList I)[(i : ℕ)]

/-- The vertex of a name in the list. -/
def idx (x : VName I) (hx : x ∈ vertexList I) : Fin (nV I) :=
  ⟨(vertexList I).idxOf x, List.idxOf_lt_length_of_mem hx⟩

lemma nm_mem (i : Fin (nV I)) : nm i ∈ vertexList I := List.getElem_mem _

lemma nm_valid (i : Fin (nV I)) : Valid I (nm i) := (mem_vertexList I _).mp (nm_mem i)

@[simp] lemma nm_idx (x : VName I) (hx : x ∈ vertexList I) : nm (idx x hx) = x :=
  List.getElem_idxOf _

@[simp] lemma idx_nm (i : Fin (nV I)) : idx (nm i) (nm_mem i) = i :=
  Fin.ext ((nodup_vertexList I).idxOf_getElem i i.2)

lemma nm_injective : Function.Injective (nm (I := I)) := by
  intro i j h
  rw [← idx_nm i, ← idx_nm j]
  simp only [idx, h]

lemma matrixGraph_n (ε : ZMod 2) : (matrixGraph I ε).n = nV I := rfl

lemma matrixGraph_adj (ε : ZMod 2) (i j : Fin (nV I)) :
    (matrixGraph I ε).graph.Adj i j ↔ adjN I ε (nm i) (nm j) := Iff.rfl

lemma matrixGraph_color (ε ε' : ZMod 2) (i j : Fin (nV I)) :
    (matrixGraph I ε).color i = (matrixGraph I ε').color j ↔ (nm i).1 = (nm j).1 :=
  listGraph_color_eq_iff (vertexList I) (adjN I ε) (adjN_symm I ε) (adjN_irrefl I ε) Prod.fst i j

/-! ### The translation on vertices -/

/-- The bijection of a description on vertices. -/
def phiV (D : Desc I) (i : Fin (nV I)) : Fin (nV I) :=
  idx (phi D (nm i)) ((mem_vertexList I _).mpr (valid_phi D (nm_valid i)))

@[simp] lemma nm_phiV (D : Desc I) (i : Fin (nV I)) : nm (phiV D i) = phi D (nm i) := nm_idx _ _

lemma phiV_phiV (D : Desc I) (i : Fin (nV I)) : phiV D (phiV D i) = i :=
  nm_injective (by rw [nm_phiV, nm_phiV, phi_phi])

lemma phi_congr {D D' : Desc I} {x : VName I} (h : shift D' x.1 = shift D x.1) :
    phi D' x = phi D x := by
  simp only [phi, h]

/-! ### Game states -/

local notation "G₀" => matrixGraph I 0
local notation "G₁" => matrixGraph I 1

/-- The classes of the vertices of `G₀` carrying a pebble. -/
def clsOf {m : ℕ} (S : GameState m G₀ G₁) : Finset (ICls I) :=
  Finset.univ.biUnion fun j => match S j with
    | some (p, _) => {(nm p).1}
    | none => ∅

lemma mem_clsOf {m : ℕ} {S : GameState m G₀ G₁} {X : ICls I} :
    X ∈ clsOf S ↔ ∃ j p q, S j = some (p, q) ∧ (nm p).1 = X := by
  simp only [clsOf, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    split at hj
    · next p q h => exact ⟨j, p, q, h, (Finset.mem_singleton.mp hj).symm⟩
    · simp at hj
  · rintro ⟨j, p, q, h, rfl⟩
    exact ⟨j, by simp [h]⟩

lemma clsOf_valid {m : ℕ} (S : GameState m G₀ G₁) : AllValid (clsOf S) := by
  intro X hX
  obtain ⟨j, p, q, -, rfl⟩ := mem_clsOf.mp hX
  exact (nm_valid p).1

lemma card_clsOf_lift {m : ℕ} (S : GameState (m + 1) G₀ G₁) (i : Fin (m + 1)) :
    (clsOf (Function.update S i none)).card ≤ m := by
  classical
  refine (Finset.card_biUnion_le).trans ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self, Finset.card_empty, zero_add]
  calc _ ≤ ∑ j ∈ Finset.univ.erase i, 1 := Finset.sum_le_sum fun j _ => by
          split <;> simp
    _ = m := by simp

lemma clsOf_lift_subset {m : ℕ} (S : GameState m G₀ G₁) (i : Fin m) :
    clsOf (Function.update S i none) ⊆ clsOf S := by
  intro X hX
  obtain ⟨j, p, q, h, rfl⟩ := mem_clsOf.mp hX
  by_cases hji : j = i
  · subst hji; simp at h
  · rw [Function.update_of_ne hji] at h
    exact mem_clsOf.mpr ⟨j, p, q, h, rfl⟩

lemma clsOf_place {m : ℕ} (S : GameState m G₀ G₁) (i : Fin m) (p q : Fin (nV I)) :
    clsOf (Function.update S i (some (p, q))) = insert (nm p).1 (clsOf (Function.update S i none)) := by
  ext X
  simp only [mem_clsOf, Finset.mem_insert]
  constructor
  · rintro ⟨j, p', q', h, rfl⟩
    by_cases hji : j = i
    · subst hji; simp at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inl rfl
    · rw [Function.update_of_ne hji] at h
      exact Or.inr ⟨j, p', q', by rw [Function.update_of_ne hji]; exact h, rfl⟩
  · rintro (rfl | ⟨j, p', q', h, rfl⟩)
    · exact ⟨i, p, q, by simp, rfl⟩
    · by_cases hji : j = i
      · subst hji; simp at h
      · exact ⟨j, p', q', by rw [Function.update_of_ne hji] at h ⊢; exact h, rfl⟩

/-- The pebble pairs follow the translation of `D`. -/
def Matches {m : ℕ} (D : Desc I) (S : GameState m G₀ G₁) : Prop :=
  ∀ j p q, S j = some (p, q) → q = phiV D p

/-- Consistent descriptions give partial isomorphisms. -/
lemma partialIso_of_good {m r : ℕ} {D : Desc I} {S : GameState m G₀ G₁}
    (hG : Good r (clsOf S) D) (hM : Matches D S) : IsPartialIso G₀ G₁ S := by
  intro i j p q p' q' hi hj
  have hpA : (nm p).1 ∈ clsOf S := mem_clsOf.mpr ⟨i, p, q, hi, rfl⟩
  have hp'A : (nm p').1 ∈ clsOf S := mem_clsOf.mpr ⟨j, p', q', hj, rfl⟩
  have e1 := hM i p q hi
  have e2 := hM j p' q' hj
  subst e1 e2
  refine ⟨⟨fun h => h ▸ rfl, fun h => ?_⟩, ?_, ?_⟩
  · have := congrArg (phiV D) h
    erw [phiV_phiV, phiV_phiV] at this
    exact this
  · show adjN I 0 (nm p) (nm p') ↔ adjN I 1 (nm (phiV D p)) (nm (phiV D p'))
    erw [nm_phiV, nm_phiV]
    exact adjN_phi D hG.init (nm_valid p) (nm_valid p') (hG.ms_link hpA) (hG.ms_link hp'A)
  · exact (matrixGraph_color 0 1 p (phiV D p)).mpr (by erw [nm_phiV, phi_fst])

/-- Duplicator's invariant on game states. -/
def DupInv {m : ℕ} (r : ℕ) (S : GameState m G₀ G₁) : Prop :=
  ∃ D : Desc I, Good r (clsOf S) D ∧ Matches D S

/-- **Duplicator's strategy.** -/
theorem survivesFrom_of_inv (hk : 2 ≤ k) :
    ∀ (r : ℕ) (S : GameState (k + 1) G₀ G₁), DupInv r S → SurvivesFrom G₀ G₁ r S
  | 0, _, _ => trivial
  | r + 1, S, ⟨D, hG, hM⟩ => by
    classical
    intro i
    set A₀ := clsOf (Function.update S i none)
    have hG₀ : Good (r + 1) A₀ D := hG.mono le_rfl (clsOf_lift_subset S i)
    have hA₀ := clsOf_valid (Function.update S i none)
    have hcard := card_clsOf_lift S i
    have hext : ∀ X : ICls I, ∃ D' : Desc I, ClsValid I X →
        Good r (insert X A₀) D' ∧ ∀ Y ∈ A₀, shift D' Y = shift D Y := by
      intro X
      by_cases hX : ClsValid I X
      · obtain ⟨D', h1, h2⟩ := extend hk hG₀ hA₀ hcard hX
        exact ⟨D', fun _ => ⟨h1, h2⟩⟩
      · exact ⟨D, fun h => absurd h hX⟩
    choose DX hDX using hext
    let f : Fin (nV I) → Fin (nV I) := fun p => phiV (DX (nm p).1) p
    have hf : Function.Involutive f := by
      intro p
      have : (nm (f p)).1 = (nm p).1 := by simp [f]
      simp only [f, this, phiV_phiV]
    refine ⟨hf.toPerm f, fun p => ?_⟩
    have hp := hDX (nm p).1 (nm_valid p).1
    set S' := Function.update S i (some (p, (hf.toPerm f) p))
    have hcls : clsOf S' = insert (nm p).1 A₀ := clsOf_place S i p _
    have hM' : Matches (DX (nm p).1) S' := by
      intro j p' q' hj
      by_cases hji : j = i
      · subst hji
        simp only [S', Function.update_self, Option.some.injEq] at hj
        obtain ⟨rfl, rfl⟩ := hj
        rfl
      · rw [show S' j = S j from Function.update_of_ne hji _ _] at hj
        rw [hM j p' q' hj]
        have hY : (nm p').1 ∈ A₀ :=
          mem_clsOf.mpr ⟨j, p', q', by rw [Function.update_of_ne hji]; exact hj, rfl⟩
        apply nm_injective
        erw [nm_phiV, nm_phiV, phi_congr (hp.2 _ hY)]
    have hG' : Good r (clsOf S') (DX (nm p).1) := hcls ▸ hp.1
    exact ⟨partialIso_of_good hG' hM', survivesFrom_of_inv hk r S' ⟨_, hG', hM'⟩⟩

/-- **Part (II) of the matrix compiler.** Duplicator survives `r` rounds as long as `K_r` is
conflict-free. -/
theorem duplicatorSurvives (hk : 2 ≤ k) {r : ℕ} (hnc : ¬ I.toParitySystem.HasConflict r) :
    DuplicatorSurvives (k + 1) r (matrixGraph I 0) (matrixGraph I 1) := by
  refine ⟨rfl, survivesFrom_of_inv hk r _ ⟨desc0 I, ?_, fun _ _ _ h => by simp at h⟩⟩
  have : clsOf (I := I) (fun _ : Fin (k + 1) => none) = ∅ := by
    ext X; simp [mem_clsOf]
  rw [this]
  exact good_empty (by omega) hnc

end Lax119563Proofs.Matrix
