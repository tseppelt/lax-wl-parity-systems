import Mathlib
import Lax119563.WeisfeilerLeman

/-!
# A crude stabilization bound for `k`-WL on a pair of graphs

If `k`-WL distinguishes `G` and `H` at all, then it does so after at most
`|V(G)|^k + |V(H)|^k` rounds. We consider the joint coloring of the disjoint union of the
`k`-tuples of both graphs. The number of its color classes never decreases; once it does not
increase in one round, the partition is stable forever, and every later distinction is
already visible at that round.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman

namespace Lax119563Proofs.Counter

variable {k : ℕ} (G H : ColoredGraph)

instance color_nonempty (k : ℕ) : ∀ r, Nonempty (Color k r)
  | 0 => ⟨(⟨fun _ _ => true, fun _ _ => true, fun _ => 0⟩ : AtomicType k)⟩
  | r + 1 => by
    have := color_nonempty k r
    exact ⟨((Classical.arbitrary (Color k r), 0) : Color k r × Multiset (Fin k → Color k r))⟩

/-- The colors of the `k`-tuples of both graphs. -/
noncomputable def jointColor (r : ℕ) :
    (Fin k → Fin G.n) ⊕ (Fin k → Fin H.n) → Color k r
  | .inl p => color G r p
  | .inr q => color H r q

/-- The previous color, the first component of a color of round `r + 1`. -/
def prevColor {r : ℕ} (c : Color k (r + 1)) : Color k r := c.1

theorem jointColor_succ_fst (r : ℕ) (x : (Fin k → Fin G.n) ⊕ (Fin k → Fin H.n)) :
    (jointColor G H (r + 1) x).1 = jointColor G H r x := by
  cases x <;> rfl

theorem jointColor_eq_of_succ {r : ℕ} {x y : (Fin k → Fin G.n) ⊕ (Fin k → Fin H.n)}
    (h : jointColor G H (r + 1) x = jointColor G H (r + 1) y) :
    jointColor G H r x = jointColor G H r y := by
  rw [← jointColor_succ_fst, h, jointColor_succ_fst]

theorem jointColor_eq_of_le {r r' : ℕ} (hr : r ≤ r')
    {x y : (Fin k → Fin G.n) ⊕ (Fin k → Fin H.n)}
    (h : jointColor G H r' x = jointColor G H r' y) :
    jointColor G H r x = jointColor G H r y := by
  induction r', hr using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact ih (jointColor_eq_of_succ G H h)

/-- The partition of round `r` is not refined in round `r + 1`. -/
def Stable (r : ℕ) : Prop :=
  ∀ x y : (Fin k → Fin G.n) ⊕ (Fin k → Fin H.n),
    jointColor G H r x = jointColor G H r y → jointColor G H (r + 1) x = jointColor G H (r + 1) y

theorem stable_succ {r : ℕ} (hs : Stable (k := k) G H r) : Stable (k := k) G H (r + 1) := by
  classical
  -- the colors of round `r + 1` are a function of the colors of round `r`
  let g : Color k r → Color k (r + 1) := fun c =>
    if h : ∃ x, jointColor G H r x = c then jointColor G H (r + 1) h.choose
    else Classical.arbitrary _
  have hg : ∀ x, jointColor G H (r + 1) x = g (jointColor G H r x) := by
    intro x
    have h : ∃ y, jointColor G H r y = jointColor G H r x := ⟨x, rfl⟩
    simp only [g, dif_pos h]
    exact hs _ _ h.choose_spec.symm
  have hG : ∀ p : Fin k → Fin G.n, color G (r + 1) p = g (color G r p) :=
    fun p => hg (.inl p)
  have hH : ∀ q : Fin k → Fin H.n, color H (r + 1) q = g (color H r q) :=
    fun q => hg (.inr q)
  have hsnd : ∀ x, (jointColor G H (r + 2) x).2 =
      (jointColor G H (r + 1) x).2.map (fun t i => g (t i)) := by
    intro x
    cases x with
    | inl p =>
      show (Finset.univ : Finset (Fin G.n)).val.map
          (fun q i => color G (r + 1) (Function.update p i q)) =
        ((Finset.univ : Finset (Fin G.n)).val.map
          (fun q i => color G r (Function.update p i q))).map (fun t i => g (t i))
      rw [Multiset.map_map]
      congr 1
      funext q
      funext i
      exact hG _
    | inr p =>
      show (Finset.univ : Finset (Fin H.n)).val.map
          (fun q i => color H (r + 1) (Function.update p i q)) =
        ((Finset.univ : Finset (Fin H.n)).val.map
          (fun q i => color H r (Function.update p i q))).map (fun t i => g (t i))
      rw [Multiset.map_map]
      congr 1
      funext q
      funext i
      exact hH _
  intro x y hxy
  have h1 : (jointColor G H (r + 2) x).1 = (jointColor G H (r + 2) y).1 := by
    rw [jointColor_succ_fst, jointColor_succ_fst, hxy]
  have h2 : (jointColor G H (r + 2) x).2 = (jointColor G H (r + 2) y).2 := by
    rw [hsnd, hsnd, hxy]
  exact Prod.ext h1 h2

theorem stable_add {r : ℕ} (hs : Stable (k := k) G H r) (d : ℕ) :
    Stable (k := k) G H (r + d) := by
  induction d with
  | zero => exact hs
  | succ d ih => exact stable_succ G H ih

theorem jointColor_eq_iff_of_stable {r : ℕ} (hs : Stable (k := k) G H r) (d : ℕ)
    (x y : (Fin k → Fin G.n) ⊕ (Fin k → Fin H.n)) :
    jointColor G H (r + d) x = jointColor G H (r + d) y ↔ jointColor G H r x = jointColor G H r y := by
  refine ⟨jointColor_eq_of_le G H (Nat.le_add_right r d), fun h => ?_⟩
  induction d with
  | zero => exact h
  | succ d ih => exact stable_add G H hs d x y ih

/-- After stabilization, later distinctions are already visible. -/
theorem distinguishesAfter_of_stable {r : ℕ} (hs : Stable (k := k) G H r) {r' : ℕ}
    (hr : r ≤ r') (h : DistinguishesAfter k r' G H) : DistinguishesAfter k r G H := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  obtain ⟨c, hc⟩ := h
  by_cases hx : ∃ x, jointColor G H (r + d) x = c
  · obtain ⟨x, rfl⟩ := hx
    refine ⟨jointColor G H r x, ?_⟩
    have e1 : Nat.card {p : Fin k → Fin G.n // color G (r + d) p = jointColor G H (r + d) x} =
        Nat.card {p : Fin k → Fin G.n // color G r p = jointColor G H r x} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun p =>
        jointColor_eq_iff_of_stable G H hs d (.inl p) x)
    have e2 : Nat.card {p : Fin k → Fin H.n // color H (r + d) p = jointColor G H (r + d) x} =
        Nat.card {p : Fin k → Fin H.n // color H r p = jointColor G H r x} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun p =>
        jointColor_eq_iff_of_stable G H hs d (.inr p) x)
    rw [← e1, ← e2]
    exact hc
  · push Not at hx
    exfalso
    apply hc
    have h1 : IsEmpty {p : Fin k → Fin G.n // color G (r + d) p = c} :=
      ⟨fun p => hx (.inl p.1) p.2⟩
    have h2 : IsEmpty {p : Fin k → Fin H.n // color H (r + d) p = c} :=
      ⟨fun p => hx (.inr p.1) p.2⟩
    rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty]

open Classical in
/-- The number of color classes of round `r`. -/
noncomputable def numClasses (r : ℕ) : ℕ :=
  ((Finset.univ : Finset ((Fin k → Fin G.n) ⊕ (Fin k → Fin H.n))).image
    (jointColor G H r)).card

open Classical in
theorem image_succ (r : ℕ) :
    (Finset.univ : Finset ((Fin k → Fin G.n) ⊕ (Fin k → Fin H.n))).image (jointColor G H r) =
      ((Finset.univ : Finset ((Fin k → Fin G.n) ⊕ (Fin k → Fin H.n))).image
        (jointColor G H (r + 1))).image prevColor := by
  rw [Finset.image_image]
  congr 1
  funext x
  exact (jointColor_succ_fst G H r x).symm

open Classical in
theorem numClasses_le_succ (r : ℕ) :
    numClasses (k := k) G H r ≤ numClasses (k := k) G H (r + 1) := by
  unfold numClasses
  rw [image_succ]
  exact Finset.card_image_le

theorem numClasses_le_card (r : ℕ) :
    numClasses (k := k) G H r ≤ G.n ^ k + H.n ^ k := by
  classical
  unfold numClasses
  refine (Finset.card_image_le).trans ?_
  simp [Finset.card_univ, Fintype.card_sum]

open Classical in
theorem stable_of_numClasses_eq {r : ℕ}
    (h : numClasses (k := k) G H r = numClasses (k := k) G H (r + 1)) :
    Stable (k := k) G H r := by
  unfold numClasses at h
  rw [image_succ] at h
  have hinj := Finset.card_image_iff.mp h
  intro x y hxy
  apply hinj (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ x)))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ y)))
  exact (jointColor_succ_fst G H r x).trans (hxy.trans (jointColor_succ_fst G H r y).symm)

theorem exists_stable :
    ∃ r ≤ G.n ^ k + H.n ^ k, Stable (k := k) G H r := by
  by_contra hcon
  push Not at hcon
  have key : ∀ r ≤ G.n ^ k + H.n ^ k + 1, r ≤ numClasses (k := k) G H r := by
    intro r
    induction r with
    | zero => intro _; exact Nat.zero_le _
    | succ r ih =>
      intro hr
      have h1 := ih (by omega)
      have h2 : numClasses (k := k) G H r ≠ numClasses (k := k) G H (r + 1) := fun h =>
        hcon r (by omega) (stable_of_numClasses_eq G H h)
      have h3 := numClasses_le_succ (k := k) G H r
      omega
  have := key _ le_rfl
  have := numClasses_le_card (k := k) G H (G.n ^ k + H.n ^ k + 1)
  omega

/-- **Crude stabilization.** If `k`-WL distinguishes `G` and `H`, then it does so after at
most `|V(G)|^k + |V(H)|^k` rounds. -/
theorem exists_distinguishesAfter_le (h : Distinguishes k G H) :
    ∃ r ≤ G.n ^ k + H.n ^ k, DistinguishesAfter k r G H := by
  obtain ⟨r', hr'⟩ := h
  obtain ⟨r, hr, hs⟩ := exists_stable (k := k) G H
  by_cases hle : r ≤ r'
  · exact ⟨r, hr, distinguishesAfter_of_stable G H hs hle hr'⟩
  · exact ⟨r', by omega, hr'⟩

end Lax119563Proofs.Counter
