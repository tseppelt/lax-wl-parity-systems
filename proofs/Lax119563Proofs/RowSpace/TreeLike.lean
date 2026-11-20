import Mathlib
import Lax119563.ContradictionTrees

/-!
# Tree-like linear systems and contradiction trees

A list of equations is *tree-like* if every equation shares at most one variable with the
equations after it in the list (so its incidence graph is a forest). If a tree-like system of
equations of a parity system `P`, together with a set `U` of initial facts of `P`, has no
solution over `𝔽₂`, then `P` has a contradiction tree with at most
`1 + #equations + #U` nodes. Contradiction trees also transfer along maps of parity systems
that send equations injectively onto equations and initial facts to initial facts.
-/

open Lax119563.ParitySystems Lax119563.ContradictionTrees

namespace Lax119563Proofs.RowSpace

/-- The union of a list of finite sets. -/
def unionAll {V : Type*} [DecidableEq V] (hs : List (Finset V)) : Finset V :=
  hs.foldr (· ∪ ·) ∅

/-- Every equation shares at most one variable with the later ones. -/
inductive TreeLike {V : Type*} [DecidableEq V] : List (Finset V) → Prop
  | nil : TreeLike []
  | cons {h : Finset V} {hs : List (Finset V)} :
      (h ∩ unionAll hs).card ≤ 1 → TreeLike hs → TreeLike (h :: hs)

/-- Size bounds of contradiction trees are monotone. -/
theorem HasContradictionWithin.mono {V : Type*} [DecidableEq V] {P : ParitySystem V}
    {s s' : ℕ} (h : HasContradictionWithin P s) (hss : s ≤ s') :
    HasContradictionWithin P s' := by
  obtain ⟨X, s₀, s₁, h₀, h₁, hs⟩ := h
  exact ⟨X, s₀, s₁, h₀, h₁, hs.trans hss⟩

theorem subset_unionAll {V : Type*} [DecidableEq V] {hs : List (Finset V)} {g : Finset V}
    (hg : g ∈ hs) : g ⊆ unionAll hs := by
  induction hs with
  | nil => simp at hg
  | cons a t ih =>
    show g ⊆ a ∪ unionAll t
    rcases List.mem_cons.mp hg with rfl | hg
    · exact Finset.subset_union_left
    · exact (ih hg).trans Finset.subset_union_right

theorem zmod2_cases : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide

theorem zmod2_add_self : ∀ b : ZMod 2, b + b = 0 := by decide

/-- Two derivable facts `(X, 0), (X, 1) ∈ U` give a contradiction tree. -/
theorem hasContradiction_of_pair {V : Type*} [DecidableEq V] {P : ParitySystem V}
    {U : Finset (V × ZMod 2)} {sz : V × ZMod 2 → ℕ}
    (hU : ∀ u ∈ U, HasDerivationWithin P u (sz u)) {X : V} (h0 : (X, 0) ∈ U)
    (h1 : (X, 1) ∈ U) : HasContradictionWithin P (1 + ∑ u ∈ U, sz u) := by
  refine ⟨X, sz (X, 0), sz (X, 1), hU _ h0, hU _ h1, ?_⟩
  have hne : (X, (0 : ZMod 2)) ≠ (X, 1) := by simp
  have hsub : ({(X, 0), (X, 1)} : Finset (V × ZMod 2)) ⊆ U := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl <;> assumption
  have := Finset.sum_le_sum_of_subset (f := sz) hsub
  rw [Finset.sum_pair hne] at this
  omega

/-- Facts without a conflict are satisfiable. -/
theorem solve_facts {V : Type*} [DecidableEq V] (U : Finset (V × ZMod 2))
    (hU : ¬ ∃ X, (X, 0) ∈ U ∧ (X, 1) ∈ U) :
    ∀ u ∈ U, (fun X => if (X, (1 : ZMod 2)) ∈ U then (1 : ZMod 2) else 0) u.1 = u.2 := by
  rintro ⟨X, b⟩ hu
  rcases zmod2_cases b with rfl | rfl
  · show (if (X, (1 : ZMod 2)) ∈ U then (1 : ZMod 2) else 0) = 0
    rw [if_neg]
    intro h1
    exact hU ⟨X, hu, h1⟩
  · show (if (X, (1 : ZMod 2)) ∈ U then (1 : ZMod 2) else 0) = 1
    rw [if_pos hu]

/-- Generalization of `hasContradiction_of_unsolvable` to derivable facts with sizes. -/
theorem hasContradiction_aux {V : Type*} [DecidableEq V] (P : ParitySystem V)
    {hs : List (Finset V)} (htl : TreeLike hs) :
    ∀ (U : Finset (V × ZMod 2)) (sz : V × ZMod 2 → ℕ), (∀ h ∈ hs, h ∈ P.equations) →
      (∀ u ∈ U, HasDerivationWithin P u (sz u)) →
      (¬ ∃ y : V → ZMod 2, (∀ h ∈ hs, ∑ x ∈ h, y x = 0) ∧ ∀ u ∈ U, y u.1 = u.2) →
      HasContradictionWithin P (1 + hs.length + ∑ u ∈ U, sz u) := by
  induction htl with
  | nil =>
    intro U sz _ hU hun
    by_cases hc : ∃ X, (X, 0) ∈ U ∧ (X, 1) ∈ U
    · obtain ⟨X, h0, h1⟩ := hc
      exact HasContradictionWithin.mono (hasContradiction_of_pair hU h0 h1) (by simp)
    · exact absurd ⟨fun X => if (X, (1 : ZMod 2)) ∈ U then (1 : ZMod 2) else 0, by simp,
        solve_facts U hc⟩ hun
  | @cons h rest hcard _ ih =>
    intro U sz hmem hU hun
    have hh : h ∈ P.equations := hmem h List.mem_cons_self
    have hmem' : ∀ g ∈ rest, g ∈ P.equations := fun g hg => hmem g (List.mem_cons_of_mem _ hg)
    obtain ⟨x, hxh, hpriv⟩ : ∃ x ∈ h, ∀ Y ∈ h.erase x, Y ∉ unionAll rest := by
      by_cases hS : ∃ z ∈ h, z ∈ unionAll rest
      · obtain ⟨z, hzh, hzr⟩ := hS
        refine ⟨z, hzh, fun Y hY hYr => ?_⟩
        have := Finset.card_le_one.mp hcard Y
          (Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase hY, hYr⟩) z
          (Finset.mem_inter.mpr ⟨hzh, hzr⟩)
        exact Finset.ne_of_mem_erase hY this
      · have hne : h.Nonempty := by
          rw [← Finset.card_pos]; rcases P.card_equation h hh with h2 | h3 <;> omega
        obtain ⟨x, hx⟩ := hne
        exact ⟨x, hx, fun Y hY hYr => hS ⟨Y, Finset.mem_of_mem_erase hY, hYr⟩⟩
    have hprivg : ∀ g ∈ rest, ∀ z ∈ g, z ∉ h.erase x := fun g hg z hz hzh =>
      hpriv z hzh (subset_unionAll hg hz)
    have hlen : (h :: rest).length = rest.length + 1 := rfl
    rw [hlen]
    by_cases hA : ∃ Y ∈ h.erase x, (Y, 0) ∈ U ∧ (Y, 1) ∈ U
    · obtain ⟨Y, -, h0, h1⟩ := hA
      exact HasContradictionWithin.mono (hasContradiction_of_pair hU h0 h1) (by omega)
    by_cases hB : ∃ Y ∈ h.erase x, (Y, 0) ∉ U ∧ (Y, 1) ∉ U
    · obtain ⟨Y, hY, h0, h1⟩ := hB
      refine HasContradictionWithin.mono (ih U sz hmem' hU ?_) (by omega)
      rintro ⟨y, hyr, hyU⟩
      apply hun
      have hYh := Finset.mem_of_mem_erase hY
      refine ⟨Function.update y Y (∑ z ∈ h.erase Y, y z), ?_, ?_⟩
      · intro g hg
        rcases List.mem_cons.mp hg with hgh | hg
        · rw [hgh, ← Finset.add_sum_erase _ _ hYh, Function.update_self]
          have : ∑ z ∈ h.erase Y, Function.update y Y (∑ z ∈ h.erase Y, y z) z
              = ∑ z ∈ h.erase Y, y z :=
            Finset.sum_congr rfl (fun z hz =>
              Function.update_of_ne (Finset.ne_of_mem_erase hz) _ _)
          rw [this]
          exact zmod2_add_self _
        · rw [← hyr g hg]
          exact Finset.sum_congr rfl (fun z hz =>
            Function.update_of_ne (fun (hzY : z = Y) => hprivg g hg z hz (hzY ▸ hY)) _ _)
      · rintro ⟨Z, c⟩ hu
        have hZY : Z ≠ Y := by
          rintro rfl
          rcases zmod2_cases c with rfl | rfl
          · exact h0 hu
          · exact h1 hu
        rw [Function.update_of_ne hZY]
        exact hyU _ hu
    push Not at hA hB
    obtain ⟨b, hbmem, hbuniq⟩ : ∃ b : V → ZMod 2, (∀ Y ∈ h.erase x, (Y, b Y) ∈ U) ∧
        ∀ u ∈ U, u.1 ∈ h.erase x → u.2 = b u.1 := by
      refine ⟨fun Y => if (Y, (1 : ZMod 2)) ∈ U then 1 else 0, ?_, ?_⟩
      · intro Y hY
        by_cases h1 : (Y, (1 : ZMod 2)) ∈ U
        · simp only [if_pos h1]; exact h1
        · simp only [if_neg h1]; by_contra h0; exact h1 (hB Y hY h0)
      · rintro ⟨Z, c⟩ hu hZ
        rcases zmod2_cases c with rfl | rfl
        · show (0 : ZMod 2) = if (Z, (1 : ZMod 2)) ∈ U then 1 else 0
          rw [if_neg (hA Z hZ hu)]
        · show (1 : ZMod 2) = if (Z, (1 : ZMod 2)) ∈ U then 1 else 0
          rw [if_pos hu]
    obtain ⟨c, hc⟩ : ∃ c : ZMod 2, c = ∑ Y ∈ h.erase x, b Y := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d : ℕ, d = 1 + ∑ Y ∈ h.erase x, sz (Y, b Y) := ⟨_, rfl⟩
    have hder : HasDerivationWithin P (x, c) d := by
      rw [hc, hd]
      exact .infer b (fun Y => sz (Y, b Y)) hh hxh (fun Y hY => hU _ (hbmem Y hY)) le_rfl
    obtain ⟨U', hU'⟩ : ∃ U' : Finset (V × ZMod 2),
        U' = U.filter (fun u => u.1 ∉ h.erase x ∧ u ≠ (x, c)) := ⟨_, rfl⟩
    have hmemU' : ∀ u, u ∈ U' ↔ u ∈ U ∧ u.1 ∉ h.erase x ∧ u ≠ (x, c) := by
      intro u; rw [hU', Finset.mem_filter]
    let sz' : V × ZMod 2 → ℕ := fun u => if u = (x, c) then d else sz u
    have hxc : (x, c) ∉ U' := fun hm => ((hmemU' _).mp hm).2.2 rfl
    have hU'' : ∀ u ∈ insert (x, c) U', HasDerivationWithin P u (sz' u) := by
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · simp only [sz', if_pos rfl]; exact hder
      · have hu' := (hmemU' u).mp hu
        simp only [sz', if_neg hu'.2.2]; exact hU u hu'.1
    have hun'' : ¬ ∃ y : V → ZMod 2, (∀ g ∈ rest, ∑ z ∈ g, y z = 0) ∧
        ∀ u ∈ insert (x, c) U', y u.1 = u.2 := by
      rintro ⟨y, hyr, hyU⟩
      apply hun
      have hyx : y x = c := hyU (x, c) (Finset.mem_insert_self _ _)
      refine ⟨fun Z => if Z ∈ h.erase x then b Z else y Z, ?_, ?_⟩
      · intro g hg
        rcases List.mem_cons.mp hg with hgh | hg
        · rw [hgh, ← Finset.add_sum_erase _ _ hxh]
          have e1 : (if x ∈ h.erase x then b x else y x) = c := by
            rw [if_neg (Finset.notMem_erase x h), hyx]
          have e2 : ∑ z ∈ h.erase x, (if z ∈ h.erase x then b z else y z) = c := by
            rw [hc]; exact Finset.sum_congr rfl (fun z hz => if_pos hz)
          simp only [e1, e2]
          exact zmod2_add_self _
        · rw [← hyr g hg]
          exact Finset.sum_congr rfl (fun z hz => if_neg (hprivg g hg z hz))
      · intro u hu
        by_cases hux : u.1 ∈ h.erase x
        · simp only [if_pos hux]; exact (hbuniq u hu hux).symm
        · simp only [if_neg hux]
          by_cases hxc' : u = (x, c)
          · subst hxc'; exact hyx
          · exact hyU u (Finset.mem_insert_of_mem ((hmemU' u).mpr ⟨hu, hux, hxc'⟩))
    refine HasContradictionWithin.mono (ih (insert (x, c) U') sz' hmem' hU'' hun'') ?_
    rw [Finset.sum_insert hxc]
    have h1 : sz' (x, c) = d := if_pos rfl
    have h2 : ∑ u ∈ U', sz' u = ∑ u ∈ U', sz u :=
      Finset.sum_congr rfl (fun u hu => if_neg ((hmemU' u).mp hu).2.2)
    have hT : ∑ u ∈ (h.erase x).image (fun Y => (Y, b Y)), sz u
        = ∑ Y ∈ h.erase x, sz (Y, b Y) :=
      Finset.sum_image (fun Y _ Z _ hYZ => congrArg Prod.fst hYZ)
    have hdisj : Disjoint ((h.erase x).image (fun Y => (Y, b Y))) U' := by
      rw [Finset.disjoint_left]
      intro u huT huU
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp huT
      exact ((hmemU' _).mp huU).2.1 hY
    have hsub : (h.erase x).image (fun Y => (Y, b Y)) ∪ U' ⊆ U := by
      intro u hu
      rcases Finset.mem_union.mp hu with hu | hu
      · obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hu; exact hbmem Y hY
      · exact ((hmemU' u).mp hu).1
    have := Finset.sum_le_sum_of_subset (f := sz) hsub
    rw [Finset.sum_union hdisj, hT] at this
    rw [h1, h2]
    omega

/-- **Unsolvable tree-like systems give contradiction trees.** -/
theorem hasContradiction_of_unsolvable {V : Type*} [DecidableEq V] (P : ParitySystem V)
    {hs : List (Finset V)} (htl : TreeLike hs) (hmem : ∀ h ∈ hs, h ∈ P.equations)
    (U : Finset (V × ZMod 2)) (hU : ∀ u ∈ U, u ∈ P.initial)
    (hun : ¬ ∃ y : V → ZMod 2, (∀ h ∈ hs, ∑ x ∈ h, y x = 0) ∧ ∀ u ∈ U, y u.1 = u.2) :
    HasContradictionWithin P (1 + hs.length + U.card) := by
  have := hasContradiction_aux P htl U (fun _ => 1) hmem
    (fun u hu => .initial (hU u hu) le_rfl) hun
  simpa using this

/-- Derivation trees transfer along maps as in `HasContradictionWithin.map`. -/
theorem HasDerivationWithin.map {V W : Type*} [DecidableEq V] [DecidableEq W]
    {P : ParitySystem V} {Q : ParitySystem W} (f : V → W)
    (heq : ∀ h ∈ P.equations, Set.InjOn f (h : Set V) ∧ h.image f ∈ Q.equations)
    (hinit : ∀ u ∈ P.initial, (f u.1, u.2) ∈ Q.initial) {u : V × ZMod 2} {s : ℕ}
    (hd : HasDerivationWithin P u s) : HasDerivationWithin Q (f u.1, u.2) s := by
  induction hd with
  | initial hf hs => exact .initial (hinit _ hf) hs
  | @infer X h s b size hh hX children hs ih =>
    obtain ⟨hinj, hQ⟩ := heq h hh
    have : Nonempty V := ⟨X⟩
    obtain ⟨g, hg⟩ : ∃ g : W → V, g = Function.invFunOn f (h : Set V) := ⟨_, rfl⟩
    have key : ∀ Y ∈ h, g (f Y) = Y := fun Y hY => by
      rw [hg]; exact hinj.leftInvOn_invFunOn hY
    have hE : (h.image f).erase (f X) = (h.erase X).image f := by
      ext Z
      simp only [Finset.mem_erase, Finset.mem_image]
      constructor
      · rintro ⟨hne, Y, hY, rfl⟩
        exact ⟨Y, ⟨fun hYX => hne (congrArg f hYX), hY⟩, rfl⟩
      · rintro ⟨Y, ⟨hYX, hY⟩, rfl⟩
        exact ⟨fun he => hYX (hinj hY hX he), Y, hY, rfl⟩
    have hinj' : Set.InjOn f ((h.erase X : Finset V) : Set V) :=
      hinj.mono (fun Y hY => Finset.mem_of_mem_erase hY)
    have e1 : ∑ Y ∈ h.erase X, b Y = ∑ Z ∈ (h.image f).erase (f X), b (g Z) := by
      rw [hE, Finset.sum_image hinj']
      exact Finset.sum_congr rfl (fun Y hY => by rw [key Y (Finset.mem_of_mem_erase hY)])
    have e2 : ∑ Y ∈ h.erase X, size Y = ∑ Z ∈ (h.image f).erase (f X), size (g Z) := by
      rw [hE, Finset.sum_image hinj']
      exact Finset.sum_congr rfl (fun Y hY => by rw [key Y (Finset.mem_of_mem_erase hY)])
    show HasDerivationWithin Q (f X, ∑ Y ∈ h.erase X, b Y) s
    rw [e1]
    refine .infer (fun Z => b (g Z)) (fun Z => size (g Z)) hQ (Finset.mem_image_of_mem f hX)
      ?_ (e2 ▸ hs)
    intro Z hZ
    rw [hE] at hZ
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hZ
    have hk := key Y (Finset.mem_of_mem_erase hY)
    show HasDerivationWithin Q (f Y, b (g (f Y))) (size (g (f Y)))
    rw [hk]
    exact ih Y hY

/-- **Transfer of contradiction trees** along a map sending every equation injectively onto an
equation and every initial fact to an initial fact. -/
theorem HasContradictionWithin.map {V W : Type*} [DecidableEq V] [DecidableEq W]
    {P : ParitySystem V} {Q : ParitySystem W} (f : V → W)
    (heq : ∀ h ∈ P.equations, Set.InjOn f (h : Set V) ∧ h.image f ∈ Q.equations)
    (hinit : ∀ u ∈ P.initial, (f u.1, u.2) ∈ Q.initial) {s : ℕ}
    (h : HasContradictionWithin P s) : HasContradictionWithin Q s := by
  obtain ⟨X, s₀, s₁, h₀, h₁, hs⟩ := h
  exact ⟨f X, s₀, s₁, HasDerivationWithin.map f heq hinit h₀,
    HasDerivationWithin.map f heq hinit h₁, hs⟩

end Lax119563Proofs.RowSpace
