import Mathlib.Logic.Equiv.Basic
import Lax119563.PebbleGame
import Lax119563.GameCharacterization

/-!
# Transfer of the pebble game along renumberings with junk vertices

Two pairs of colored graphs `(G₀, G₁)` on `Fin n` and `(G'₀, G'₁)` on `Fin n'`, each pair with a
common color function, are *corresponding* if, after removing a set of *junk* vertices in each
pair (isolated in both graphs of the pair, with colors not used by any other vertex), there is a
bijection of the remaining vertices preserving adjacency in both graphs and the equality of
colors. Then if Duplicator survives `r` rounds of the bijective `m`-pebble game on the first
pair, she survives `r` rounds on the second (`survivesFrom_transfer`).
-/

open Lax119563.ColoredGraphs Lax119563.PebbleGame

namespace Lax119563Proofs.Compiler

/-- The colored graph with vertex set `Fin n`, edges `A` and colors `χ`. -/
abbrev mkGraph (n : ℕ) (A : SimpleGraph (Fin n)) (χ : Fin n → ℕ) : ColoredGraph := ⟨n, A, χ⟩

/-- A pair of graphs on `Fin n` with common colors `χ` and a set `J` of junk vertices. -/
structure JunkPair (n : ℕ) where
  A₀ : SimpleGraph (Fin n)
  A₁ : SimpleGraph (Fin n)
  χ : Fin n → ℕ
  J : Fin n → Prop
  iso₀ : ∀ u v, J u → ¬ A₀.Adj u v
  iso₁ : ∀ u v, J u → ¬ A₁.Adj u v
  col : ∀ u v, J u → ¬ J v → χ u ≠ χ v

namespace JunkPair

variable {n n' : ℕ}

/-- The two graphs. -/
abbrev G₀ (P : JunkPair n) : ColoredGraph := mkGraph n P.A₀ P.χ
/-- The two graphs. -/
abbrev G₁ (P : JunkPair n) : ColoredGraph := mkGraph n P.A₁ P.χ

end JunkPair

/-- A correspondence between the non-junk parts of two junk pairs. -/
structure Corr {n n' : ℕ} (P : JunkPair n) (Q : JunkPair n') where
  f : {u // ¬ P.J u} ≃ {u // ¬ Q.J u}
  adj₀ : ∀ u v : {u // ¬ P.J u}, P.A₀.Adj u.1 v.1 ↔ Q.A₀.Adj (f u).1 (f v).1
  adj₁ : ∀ u v : {u // ¬ P.J u}, P.A₁.Adj u.1 v.1 ↔ Q.A₁.Adj (f u).1 (f v).1
  col : ∀ u v : {u // ¬ P.J u}, P.χ u.1 = P.χ v.1 ↔ Q.χ (f u).1 = Q.χ (f v).1

namespace Corr

variable {n n' : ℕ} {P : JunkPair n} {Q : JunkPair n'}

/-- The inverse correspondence. -/
def symm (C : Corr P Q) : Corr Q P where
  f := C.f.symm
  adj₀ u v := by rw [C.adj₀ (C.f.symm u) (C.f.symm v)]; simp
  adj₁ u v := by rw [C.adj₁ (C.f.symm u) (C.f.symm v)]; simp
  col u v := by rw [C.col (C.f.symm u) (C.f.symm v)]; simp

end Corr

section Mono

variable {m : ℕ} {G H : ColoredGraph}

/-- `S` is obtained from `T` by lifting some pebbles. -/
def SubState (S T : GameState m G H) : Prop := ∀ i, S i = none ∨ S i = T i

lemma SubState.update {S T : GameState m G H} (h : SubState S T) (i : Fin m)
    (x : Option (Fin G.n × Fin H.n)) :
    SubState (Function.update S i x) (Function.update T i x) := by
  intro j
  by_cases hj : j = i
  · subst hj; simp
  · simp only [Function.update_of_ne hj]; exact h j

lemma isPartialIso_sub {S T : GameState m G H} (hT : IsPartialIso G H T) (h : SubState S T) :
    IsPartialIso G H S := by
  intro i j p q p' q' hi hj
  rcases h i with h1 | h1
  · rw [h1] at hi; cases hi
  rcases h j with h2 | h2
  · rw [h2] at hj; cases hj
  exact hT i j p q p' q' (h1 ▸ hi) (h2 ▸ hj)

lemma survivesFrom_sub : ∀ (r : ℕ) {S T : GameState m G H}, SurvivesFrom G H r T →
    SubState S T → SurvivesFrom G H r S
  | 0, _, _, _, _ => trivial
  | r + 1, S, T, hT, h => by
    intro i
    obtain ⟨f, hf⟩ := hT i
    refine ⟨f, fun p => ⟨isPartialIso_sub (hf p).1 (h.update i _), survivesFrom_sub r (hf p).2 (h.update i _)⟩⟩

lemma survivesFrom_of_isEmpty (hG : G.n = 0) (hH : H.n = 0) :
    ∀ (r : ℕ) (S : GameState m G H), SurvivesFrom G H r S
  | 0, _ => trivial
  | r + 1, S => by
    intro i
    have e : Fin G.n ≃ Fin H.n := (finCongr hG).trans (finCongr hH.symm)
    exact ⟨e, fun p => absurd p.2 (by omega)⟩

end Mono

section Transfer

variable {n n' : ℕ} {P : JunkPair n} {Q : JunkPair n'} (C : Corr P Q) {m : ℕ}

/-- Related game states: pebble pairs on non-junk vertices correspond; a lifted pebble may
correspond to a pebble pair `(p', p')` on a junk vertex. -/
def Rel (S : GameState m P.G₀ P.G₁) (S' : GameState m Q.G₀ Q.G₁) : Prop :=
  ∀ i, (∀ p q, S i = some (p, q) → ∃ (hp : ¬ P.J p) (hq : ¬ P.J q),
      S' i = some ((C.f ⟨p, hp⟩ : Fin n'), (C.f ⟨q, hq⟩ : Fin n'))) ∧
    (S i = none → S' i = none ∨ ∃ p', Q.J p' ∧ S' i = some (p', p'))

lemma Rel.update {S : GameState m P.G₀ P.G₁} {S' : GameState m Q.G₀ Q.G₁} (h : Rel C S S')
    (i : Fin m) (x : Option (Fin n × Fin n)) (x' : Option (Fin n' × Fin n'))
    (hx : (∀ p q, x = some (p, q) → ∃ (hp : ¬ P.J p) (hq : ¬ P.J q),
      x' = some ((C.f ⟨p, hp⟩ : Fin n'), (C.f ⟨q, hq⟩ : Fin n'))) ∧
      (x = none → x' = none ∨ ∃ p', Q.J p' ∧ x' = some (p', p'))) :
    Rel C (Function.update S i x) (Function.update S' i x') := by
  intro j
  by_cases hj : j = i
  · subst hj; simpa using hx
  · simp only [Function.update_of_ne hj]; exact h j

lemma Rel.isPartialIso {S : GameState m P.G₀ P.G₁} {S' : GameState m Q.G₀ Q.G₁}
    (h : Rel C S S') (hS : IsPartialIso P.G₀ P.G₁ S) : IsPartialIso Q.G₀ Q.G₁ S' := by
  -- classify the entries of `S'`
  have key : ∀ i p' q', S' i = some (p', q') →
      (∃ p q, S i = some (p, q) ∧ ∃ (hp : ¬ P.J p) (hq : ¬ P.J q),
        p' = (C.f ⟨p, hp⟩ : Fin n') ∧ q' = (C.f ⟨q, hq⟩ : Fin n')) ∨ (Q.J p' ∧ q' = p') := by
    intro i p' q' hi
    rcases hSi : S i with _ | ⟨p, q⟩
    · rcases (h i).2 hSi with h1 | ⟨r, hr, h1⟩
      · rw [h1] at hi; cases hi
      · rw [h1] at hi
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hi)
        exact Or.inr ⟨hr, rfl⟩
    · obtain ⟨hp, hq, h1⟩ := (h i).1 p q hSi
      rw [h1] at hi
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hi)
      exact Or.inl ⟨p, q, rfl, hp, hq, rfl, rfl⟩
  have notJ : ∀ (u : {u // ¬ P.J u}), ¬ Q.J (C.f u : Fin n') := fun u => (C.f u).2
  intro i j p' q' r' t' hi hj
  rcases key i p' q' hi with ⟨p, q, hSi, hp, hq, rfl, rfl⟩ | ⟨hJ, rfl⟩ <;>
  rcases key j r' t' hj with ⟨r, t, hSj, hr, ht, rfl, rfl⟩ | ⟨hJ', rfl⟩
  · obtain ⟨h1, h2, h3⟩ := hS i j p q r t hSi hSj
    refine ⟨?_, ?_, ?_⟩
    · simp only [Subtype.coe_inj, C.f.apply_eq_iff_eq, Subtype.mk.injEq]; exact h1
    · show Q.A₀.Adj _ _ ↔ Q.A₁.Adj _ _
      rw [← C.adj₀ ⟨p, hp⟩ ⟨r, hr⟩, ← C.adj₁ ⟨q, hq⟩ ⟨t, ht⟩]; exact h2
    · show Q.χ _ = Q.χ _
      exact (C.col ⟨p, hp⟩ ⟨q, hq⟩).mp h3
  · refine ⟨?_, ?_, ?_⟩
    · constructor
      · rintro rfl; exact absurd hJ' (notJ _)
      · rintro rfl; exact absurd hJ' (notJ _)
    · show Q.A₀.Adj _ _ ↔ Q.A₁.Adj _ _
      exact ⟨fun h => absurd (Q.iso₀ _ _ hJ' h.symm) id,
        fun h => absurd (Q.iso₁ _ _ hJ' h.symm) id⟩
    · obtain ⟨-, -, h3⟩ := hS i i p q p q hSi hSi
      exact (C.col ⟨p, hp⟩ ⟨q, hq⟩).mp h3
  · refine ⟨?_, ?_, ?_⟩
    · constructor
      · rintro rfl; exact absurd hJ (notJ _)
      · rintro rfl; exact absurd hJ (notJ _)
    · show Q.A₀.Adj _ _ ↔ Q.A₁.Adj _ _
      exact ⟨fun h => absurd (Q.iso₀ _ _ hJ h) id, fun h => absurd (Q.iso₁ _ _ hJ h) id⟩
    · rfl
  · refine ⟨Iff.rfl, ?_, rfl⟩
    show Q.A₀.Adj _ _ ↔ Q.A₁.Adj _ _
    exact ⟨fun h => absurd (Q.iso₀ _ _ hJ h) id, fun h => absurd (Q.iso₁ _ _ hJ h) id⟩

/-- A response of Duplicator that keeps the colors maps non-junk to non-junk vertices. -/
lemma notJ_iff_of_color {g : Fin n ≃ Fin n} (hg : ∀ p, P.χ p = P.χ (g p)) (p : Fin n) :
    ¬ P.J p ↔ ¬ P.J (g p) := by
  constructor
  · intro hp hgp
    exact P.col _ _ hgp hp (hg p).symm
  · intro hgp hp
    exact P.col _ _ hp hgp (hg p)

open Classical in
/-- The transported bijection: `f g f⁻¹` on non-junk vertices, the identity on junk. -/
noncomputable def transport (g : Fin n ≃ Fin n) (hg : ∀ p, ¬ P.J p ↔ ¬ P.J (g p)) :
    Fin n' ≃ Fin n' :=
  Equiv.Perm.subtypeCongr (p := fun u => ¬ Q.J u)
    (C.f.symm.trans ((g.subtypeEquiv hg).trans C.f))
    (Equiv.refl _)

lemma transport_core (g : Fin n ≃ Fin n) (hg : ∀ p, ¬ P.J p ↔ ¬ P.J (g p))
    (u : {u // ¬ P.J u}) :
    transport C g hg (C.f u) = (C.f ⟨g u, (hg u).mp u.2⟩ : Fin n') := by
  classical
  unfold transport
  rw [Equiv.Perm.subtypeCongr.left_apply (p := fun u => ¬ Q.J u) (a := (C.f u : Fin n')) (h := (C.f u).2)]
  simp [Equiv.subtypeEquiv]

lemma transport_junk (g : Fin n ≃ Fin n) (hg : ∀ p, ¬ P.J p ↔ ¬ P.J (g p)) (p' : Fin n')
    (hp' : Q.J p') : transport C g hg p' = p' := by
  classical
  unfold transport
  rw [Equiv.Perm.subtypeCongr.right_apply (p := fun u => ¬ Q.J u) (a := p') (h := not_not.mpr hp')]
  rfl

theorem survivesFrom_transfer :
    ∀ (r : ℕ) (S : GameState m P.G₀ P.G₁) (S' : GameState m Q.G₀ Q.G₁), Rel C S S' →
      SurvivesFrom P.G₀ P.G₁ r S → SurvivesFrom Q.G₀ Q.G₁ r S'
  | 0, _, _, _, _ => trivial
  | r + 1, S, S', hR, hS => by
    intro i
    obtain ⟨g, hg⟩ := hS i
    have hcol : ∀ p, P.χ p = P.χ (g p) := fun p => by
      have := (hg p).1 i i p (g p) p (g p) (by simp) (by simp)
      exact this.2.2
    have hJ := notJ_iff_of_color hcol
    -- the state with pebble `i` lifted
    have hlift : IsPartialIso P.G₀ P.G₁ (Function.update S i none) ∧
        SurvivesFrom P.G₀ P.G₁ r (Function.update S i none) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · refine ⟨?_, survivesFrom_of_isEmpty hn hn r _⟩
        intro j _ p _ _ _ _ _
        exact absurd p.2 (by simp [hn])
      · have hsub : SubState (Function.update S i none)
            (Function.update S i (some (⟨0, hn⟩, g ⟨0, hn⟩))) := by
          intro j
          by_cases hj : j = i
          · subst hj; simp
          · right; simp [Function.update_of_ne hj]
        exact ⟨isPartialIso_sub (hg _).1 hsub, survivesFrom_sub r (hg _).2 hsub⟩
    refine ⟨transport C g hJ, fun p' => ?_⟩
    by_cases hp' : Q.J p'
    · rw [transport_junk C g hJ p' hp']
      have hR' : Rel C (Function.update S i none) (Function.update S' i (some (p', p'))) :=
        hR.update C i none _ ⟨fun _ _ h => (by simp at h), fun _ => Or.inr ⟨p', hp', rfl⟩⟩
      exact ⟨hR'.isPartialIso C hlift.1, survivesFrom_transfer r _ _ hR' hlift.2⟩
    · set u := C.f.symm ⟨p', hp'⟩ with hu
      have hp'u : p' = (C.f u : Fin n') := by simp [hu]
      rw [hp'u, transport_core C g hJ u]
      have hR' : Rel C (Function.update S i (some ((u : Fin n), g u)))
          (Function.update S' i (some ((C.f u : Fin n'),
            (C.f ⟨g u, (hJ u).mp u.2⟩ : Fin n')))) :=
        hR.update C i _ _ ⟨fun p q h => by
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          exact ⟨u.2, (hJ u).mp u.2, rfl⟩, fun h => (by simp at h)⟩
      exact ⟨hR'.isPartialIso C (hg u).1, survivesFrom_transfer r _ _ hR' (hg u).2⟩

end Transfer

end Lax119563Proofs.Compiler
