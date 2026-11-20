import Mathlib
import Lax119563.WeisfeilerLeman

/-!
# Early distinctions by `k`-WL

If `k`-WL distinguishes `G` and `H` at all, it does so after at most
`|V(G)|^k + |V(H)|^k` rounds. We consider the joint partition of the `k`-tuples of both graphs
by their colors: it refines in every round, so it stabilizes after at most as many rounds as
there are tuples, and once stable it stays stable, so no new distinctions appear.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman

namespace Lax119563Proofs.Witness

open Classical

variable {k : ℕ} (G H : ColoredGraph)

/-- The `k`-tuples of both graphs. -/
abbrev Tup (k : ℕ) (G H : ColoredGraph) := (Fin k → Fin G.n) ⊕ (Fin k → Fin H.n)

/-- The color of a tuple of either graph after `r` rounds. -/
noncomputable def ucol (r : ℕ) : Tup k G H → Color k r
  | .inl p => color G r p
  | .inr q => color H r q

/-- The multiset part of the color after round `r + 1`. -/
noncomputable def umult (r : ℕ) : Tup k G H → Multiset (Fin k → Color k r)
  | .inl p => (Finset.univ : Finset (Fin G.n)).val.map fun q i => color G r (Function.update p i q)
  | .inr p => (Finset.univ : Finset (Fin H.n)).val.map fun q i => color H r (Function.update p i q)

theorem ucol_succ (r : ℕ) (x : Tup k G H) :
    ucol G H (r + 1) x = ((ucol G H r x, umult G H r x) : Color k r × Multiset _) := by
  cases x <;> rfl

/-- Projection of a round-`r+1` color to its round-`r` part. -/
def fstC {r : ℕ} (c : Color k (r + 1)) : Color k r :=
  Prod.fst (α := Color k r) (β := Multiset (Fin k → Color k r)) c

theorem fstC_ucol (r : ℕ) (x : Tup k G H) : fstC (ucol G H (r + 1) x) = ucol G H r x := by
  rw [ucol_succ]; rfl

theorem ucol_eq_of_succ {r : ℕ} {x y : Tup k G H} (h : ucol G H (r + 1) x = ucol G H (r + 1) y) :
    ucol G H r x = ucol G H r y := by
  rw [← fstC_ucol, h, fstC_ucol]

/-- The number of color classes of the joint partition after round `r`. -/
noncomputable def numClasses (r : ℕ) : ℕ := (Finset.univ.image (ucol (k := k) G H r)).card

theorem numClasses_le_succ (r : ℕ) : numClasses (k := k) G H r ≤ numClasses (k := k) G H (r + 1) := by
  unfold numClasses
  have : Finset.univ.image (ucol (k := k) G H r) =
      (Finset.univ.image (ucol G H (r + 1))).image fstC := by
    rw [Finset.image_image]; congr 1; funext x; exact (fstC_ucol G H r x).symm
  rw [this]; exact Finset.card_image_le

theorem numClasses_le_card (r : ℕ) : numClasses (k := k) G H r ≤ G.n ^ k + H.n ^ k := by
  unfold numClasses
  refine (Finset.card_image_le).trans ?_
  simp [Finset.card_univ, Fintype.card_sum, Fintype.card_fun]

/-- The joint partition does not split from round `r` to round `r + 1`. -/
def StableAt (r : ℕ) : Prop :=
  ∀ x y : Tup k G H, ucol G H r x = ucol G H r y → ucol G H (r + 1) x = ucol G H (r + 1) y

theorem stableAt_of_numClasses {r : ℕ} (h : numClasses (k := k) G H r = numClasses (k := k) G H (r + 1)) :
    StableAt (k := k) G H r := by
  intro x y hxy
  unfold numClasses at h
  have himg : Finset.univ.image (ucol (k := k) G H r) =
      (Finset.univ.image (ucol G H (r + 1))).image fstC := by
    rw [Finset.image_image]; congr 1; funext x; exact (fstC_ucol G H r x).symm
  rw [himg] at h
  have hinj := Finset.card_image_iff.mp h
  apply hinj (by simp) (by simp)
  rw [fstC_ucol, fstC_ucol, hxy]

theorem stableAt_succ {r : ℕ} (h : StableAt (k := k) G H r) : StableAt (k := k) G H (r + 1) := by
  intro x y hxy
  -- a map from round-`r` colors to round-`r+1` colors, valid on all realized colors
  let φ : Color k r → Color k (r + 1) := fun c =>
    if hc : ∃ z, ucol G H r z = c then ucol G H (r + 1) hc.choose else ucol G H (r + 1) x
  have hφ : ∀ z, φ (ucol G H r z) = ucol G H (r + 1) z := by
    intro z
    have hc : ∃ z', ucol G H r z' = ucol G H r z := ⟨z, rfl⟩
    simp only [φ, dif_pos hc]
    exact h _ _ hc.choose_spec
  have hmult : ∀ z, umult G H (r + 1) z = (umult G H r z).map fun f i => φ (f i) := by
    intro z
    cases z with
    | inl p =>
      simp only [umult, Multiset.map_map, Function.comp_def]
      congr 1; funext q; funext i
      exact (hφ (.inl (Function.update p i q))).symm
    | inr p =>
      simp only [umult, Multiset.map_map, Function.comp_def]
      congr 1; funext q; funext i
      exact (hφ (.inr (Function.update p i q))).symm
  rw [ucol_succ, ucol_succ] at hxy
  have h1 : ucol G H r x = ucol G H r y := (Prod.mk.inj hxy).1
  have h2 : umult G H r x = umult G H r y := (Prod.mk.inj hxy).2
  rw [ucol_succ, ucol_succ G H (r + 1) y, hmult, hmult, h2]
  congr 1
  rw [ucol_succ, ucol_succ G H r y, h1, h2]

theorem ucol_iff_of_stable {r : ℕ} (h : StableAt (k := k) G H r) {s : ℕ} (hrs : r ≤ s)
    (x y : Tup k G H) : ucol G H s x = ucol G H s y ↔ ucol G H r x = ucol G H r y := by
  induction s, hrs using Nat.le_induction with
  | base => rfl
  | succ s hrs ih =>
    have hs : StableAt (k := k) G H s := by
      clear ih
      induction s, hrs using Nat.le_induction with
      | base => exact h
      | succ s _ ih => exact stableAt_succ G H ih
    exact ⟨fun hxy => ih.mp (ucol_eq_of_succ G H hxy), fun hxy => hs _ _ (ih.mpr hxy)⟩

theorem exists_stableAt : ∃ r ≤ G.n ^ k + H.n ^ k, StableAt (k := k) G H r := by
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ r ≤ G.n ^ k + H.n ^ k, numClasses (k := k) G H r < numClasses (k := k) G H (r + 1) :=
    fun r hr => lt_of_le_of_ne (numClasses_le_succ G H r)
      (fun he => hcon r hr (stableAt_of_numClasses G H he))
  have key : ∀ r ≤ G.n ^ k + H.n ^ k + 1, r ≤ numClasses (k := k) G H r := by
    intro r hr
    induction r with
    | zero => exact Nat.zero_le _
    | succ r ih => exact lt_of_le_of_lt (ih (by omega)) (hlt r (by omega))
  have := key _ le_rfl
  have := numClasses_le_card (k := k) G H (G.n ^ k + H.n ^ k + 1)
  omega

theorem distinguishesAfter_of_stable {r s : ℕ} (hst : StableAt (k := k) G H r) (hrs : r ≤ s)
    (h : DistinguishesAfter k s G H) : DistinguishesAfter k r G H := by
  by_contra hcon
  obtain ⟨c, hc⟩ := h
  apply hc
  by_cases hz : ∃ z, ucol G H s z = c
  · obtain ⟨z, rfl⟩ := hz
    have hcount := not_not.mp (fun h' => hcon ⟨ucol G H r z, h'⟩)
    have e1 : Nat.card {p : Fin k → Fin G.n // color G s p = ucol G H s z} =
        Nat.card {p : Fin k → Fin G.n // color G r p = ucol G H r z} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun p =>
        ucol_iff_of_stable G H hst hrs (.inl p) z)
    have e2 : Nat.card {p : Fin k → Fin H.n // color H s p = ucol G H s z} =
        Nat.card {p : Fin k → Fin H.n // color H r p = ucol G H r z} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun p =>
        ucol_iff_of_stable G H hst hrs (.inr p) z)
    rw [e1, e2]; exact hcount
  · push_neg at hz
    have e1 : IsEmpty {p : Fin k → Fin G.n // color G s p = c} :=
      ⟨fun p => hz (.inl p.1) p.2⟩
    have e2 : IsEmpty {p : Fin k → Fin H.n // color H s p = c} :=
      ⟨fun p => hz (.inr p.1) p.2⟩
    simp [Nat.card_of_isEmpty]

/-- **Early distinction.** If `k`-WL distinguishes `G` and `H` after some round, it does so
after at most `|V(G)|^k + |V(H)|^k` rounds. -/
theorem exists_distinguishesAfter_le {s : ℕ} (h : DistinguishesAfter k s G H) :
    ∃ r ≤ G.n ^ k + H.n ^ k, DistinguishesAfter k r G H := by
  obtain ⟨r, hr, hst⟩ := exists_stableAt (k := k) G H
  by_cases hsr : s ≤ r
  · exact ⟨s, hsr.trans hr, h⟩
  · exact ⟨r, hr, distinguishesAfter_of_stable G H hst (by omega) h⟩

end Lax119563Proofs.Witness
