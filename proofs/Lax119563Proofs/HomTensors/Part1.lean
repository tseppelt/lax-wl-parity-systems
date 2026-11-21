import Lax119563.ColoredHomomorphisms
import Lax119563.ImplicitParitySystems
import Lax119563.ParitySystems
import Lax119563.PebbleGame
import Lax119563.RowSpaceCompiler
import Lax119563.WeisfeilerLeman
import Lax228581.Treewidth
import Mathlib

/-! ### Formerly `Lax119563Proofs.Counter.Bits` -/

section Counter_Bits

/-!
# Counter values of addresses

We fix `k = K + 1` blocks and block coordinates in `𝔽₂^ℓ`. The first `K` blocks are the
*data blocks*, the last block is the checksum block. The `m = ℓ K` data bits of an array `a`
are read row by row: data position `p = i + K t` (with `i < K`, `t < ℓ`) is bit `t` of the
block coordinate `a_i`. The *counter value* of `a` is `∑_p a_p 2^p`.

The increment at position `j` adds the shift `δ_j` flipping all data positions `≤ j` (and
updating the checksum accordingly). On arrays whose data word starts with `1^j 0`, it
increases the counter value by one.
-/

open Lax119563.ImplicitParitySystems

namespace Lax119563Proofs.Counter

variable {K ℓ : ℕ}

/-- Arrays of block coordinates with `K + 1` blocks. -/
abbrev Arr (K ℓ : ℕ) := Fin (K + 1) → BlockCoord ℓ

/-- The data position `i + K t` of row `t` and data block `i`. -/
def pos (K ℓ : ℕ) : Fin ℓ × Fin K ≃ Fin (ℓ * K) := finProdFinEquiv

theorem pos_val (x : Fin ℓ × Fin K) : (pos K ℓ x : ℕ) = x.2 + K * x.1 := by
  simp [pos, finProdFinEquiv_apply_val]

/-- The data bit at data position `p`. -/
def dbit (a : Arr K ℓ) (p : Fin (ℓ * K)) : ZMod 2 :=
  a (Fin.castSucc ((pos K ℓ).symm p).2) ((pos K ℓ).symm p).1

theorem dbit_pos (a : Arr K ℓ) (t : Fin ℓ) (i : Fin K) :
    dbit a (pos K ℓ (t, i)) = a (Fin.castSucc i) t := by
  simp [dbit]

/-- The counter value of an array. -/
def val (a : Arr K ℓ) : ℕ :=
  ∑ p : Fin (ℓ * K), (dbit a p).val * 2 ^ (p : ℕ)

/-- The data part of the shift `δ_j`: ones at all data positions `≤ j`. -/
def dataShift (K ℓ j : ℕ) (i : Fin K) : BlockCoord ℓ :=
  fun t => if (pos K ℓ (t, i) : ℕ) ≤ j then 1 else 0

/-- The shift `δ_j`, completed by the checksum. -/
def shift (K ℓ j : ℕ) : Arr K ℓ :=
  Fin.snoc (α := fun _ => BlockCoord ℓ) (dataShift K ℓ j) (∑ i, dataShift K ℓ j i)

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

theorem blockCoord_add_self (x : BlockCoord ℓ) : x + x = 0 := by
  funext t
  exact zmod2_add_self (x t)

theorem zmod2_val_one : (1 : ZMod 2).val = 1 := rfl

theorem zmod2_eq_one_of_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl h
  · rfl

theorem sum_shift (j : ℕ) : ∑ i, shift K ℓ j i = 0 := by
  rw [Fin.sum_univ_castSucc]
  simp only [shift, Fin.snoc_castSucc, Fin.snoc_last]
  exact blockCoord_add_self _

theorem dbit_add (a b : Arr K ℓ) (p : Fin (ℓ * K)) : dbit (a + b) p = dbit a p + dbit b p := rfl

theorem dbit_shift (j : ℕ) (p : Fin (ℓ * K)) :
    dbit (shift K ℓ j) p = if (p : ℕ) ≤ j then 1 else 0 := by
  simp [dbit, shift, dataShift]

/-- An array is an address iff its checksum block is the sum of its data blocks. -/
theorem last_eq_of_isAddress {a : Arr K ℓ} (ha : IsAddress a) :
    a (Fin.last K) = ∑ i : Fin K, a (Fin.castSucc i) := by
  unfold IsAddress at ha
  rw [Fin.sum_univ_castSucc] at ha
  have := congrArg (· + a (Fin.last K)) ha
  simp only [add_assoc, blockCoord_add_self, add_zero, zero_add] at this
  exact this.symm

theorem isAddress_add {a b : Arr K ℓ} (ha : IsAddress a) (hb : IsAddress b) :
    IsAddress (a + b) := by
  unfold IsAddress at *
  simp [Finset.sum_add_distrib, ha, hb]

theorem isAddress_shift (j : ℕ) : IsAddress (shift K ℓ j) := sum_shift j

/-- Addresses are determined by their data bits. -/
theorem eq_zero_of_dbit {a : Arr K ℓ} (ha : IsAddress a) (h : ∀ p, dbit a p = 0) : a = 0 := by
  have hd : ∀ i : Fin K, a (Fin.castSucc i) = 0 := by
    intro i
    funext t
    show a (Fin.castSucc i) t = 0
    rw [← dbit_pos a t i]
    exact h _
  funext i
  refine Fin.lastCases ?_ (fun i => hd i) i
  rw [last_eq_of_isAddress ha]
  simp [hd]

/-! ### Geometric sums -/

theorem geom_two (j : ℕ) : ∑ n ∈ Finset.range j, 2 ^ n + 1 = 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem sum_range_ite_lt {m j : ℕ} (hj : j ≤ m) :
    ∑ n ∈ Finset.range m, (if n < j then 2 ^ n else 0) = ∑ n ∈ Finset.range j, 2 ^ n := by
  induction m, hj using Nat.le_induction with
  | base => exact Finset.sum_congr rfl fun n hn => if_pos (Finset.mem_range.mp hn)
  | succ m hm ih => rw [Finset.sum_range_succ, ih, if_neg (by omega), add_zero]

theorem sum_fin_ite_lt {m j : ℕ} (hj : j ≤ m) :
    ∑ p : Fin m, (if (p : ℕ) < j then 2 ^ (p : ℕ) else 0) + 1 = 2 ^ j := by
  rw [Fin.sum_univ_eq_sum_range (fun n => if n < j then 2 ^ n else 0) m, sum_range_ite_lt hj,
    geom_two]

/-- Arrays whose data word starts with `1^j 0`. -/
def Prefix (j : ℕ) (a : Arr K ℓ) : Prop :=
  ∀ p : Fin (ℓ * K), (p : ℕ) ≤ j → dbit a p = if (p : ℕ) < j then 1 else 0

/-- **Increment.** Adding `δ_j` to an array with data prefix `1^j 0` increases the counter
value by one. -/
theorem val_add_shift {j : ℕ} (hj : j < ℓ * K) {a : Arr K ℓ} (ha : Prefix j a) :
    val (a + shift K ℓ j) = val a + 1 := by
  have hpt : ∀ p : Fin (ℓ * K),
      (dbit (a + shift K ℓ j) p).val * 2 ^ (p : ℕ) + (if (p : ℕ) < j then 2 ^ (p : ℕ) else 0) =
        (dbit a p).val * 2 ^ (p : ℕ) + (if (p : ℕ) = j then 2 ^ (p : ℕ) else 0) := by
    intro p
    rw [dbit_add, dbit_shift]
    rcases lt_trichotomy (p : ℕ) j with h | h | h
    · rw [ha p h.le, if_pos h, if_pos h.le, if_pos h, if_neg h.ne]
      simp [zmod2_add_self, zmod2_val_one]
    · rw [ha p h.le, if_neg (by omega), if_pos h.le, if_neg (by omega), if_pos h]
      simp [zmod2_val_one]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp
  have hsum := Finset.sum_congr rfl (fun p (_ : p ∈ Finset.univ) => hpt p)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have h1 := sum_fin_ite_lt (m := ℓ * K) hj.le
  have h2 : ∑ p : Fin (ℓ * K), (if (p : ℕ) = j then 2 ^ (p : ℕ) else 0) = 2 ^ j := by
    rw [Finset.sum_eq_single ⟨j, hj⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      exact fun h => hb (Fin.ext h)
    · simp
  unfold val
  omega

/-! ### The all-ones address -/

/-- The address `t` with all data bits `1`. -/
def top (K ℓ : ℕ) : Arr K ℓ :=
  Fin.snoc (α := fun _ => BlockCoord ℓ) (fun _ _ => 1) (fun _ => (K : ZMod 2))

theorem isAddress_top : IsAddress (top K ℓ) := by
  unfold IsAddress
  rw [Fin.sum_univ_castSucc]
  simp only [top, Fin.snoc_castSucc, Fin.snoc_last]
  funext t
  simp [zmod2_add_self]

theorem dbit_top (p : Fin (ℓ * K)) : dbit (top K ℓ) p = 1 := by
  simp [dbit, top]

theorem val_top : val (top K ℓ) + 1 = 2 ^ (ℓ * K) := by
  have := sum_fin_ite_lt (m := ℓ * K) (j := ℓ * K) le_rfl
  unfold val
  simp only [dbit_top, zmod2_val_one, one_mul]
  simpa using this

theorem val_zero : val (0 : Arr K ℓ) = 0 := by
  simp [val, dbit]

end Lax119563Proofs.Counter

end Counter_Bits

/-! ### Formerly `Lax119563Proofs.Counter.Propagation` -/

section Counter_Propagation

/-!
# Unit propagation along binary equations

Generic facts about unit propagation used for the counter: monotonicity, propagation along a
binary equation, a potential argument bounding the conflict round from below for systems of
binary equations, and the conflict round of a system that has some conflict.
-/

open Lax119563.ParitySystems

namespace Lax119563Proofs.Counter

variable {V : Type*} [DecidableEq V] (P : ParitySystem V)

theorem known_mono {r r' : ℕ} (h : r ≤ r') : P.known r ⊆ P.known r' := by
  induction r', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans Set.subset_union_left

/-- Propagation along a binary equation `X = Y`. -/
theorem known_succ_of_pair {X Y : V} (hXY : X ≠ Y) (hh : ({X, Y} : Finset V) ∈ P.equations)
    {r : ℕ} {b : ZMod 2} (hY : (Y, b) ∈ P.known r) : (X, b) ∈ P.known (r + 1) := by
  refine Or.inr ⟨{X, Y}, hh, Finset.mem_insert_self _ _, fun _ => b, ?_, ?_⟩
  · intro Z hZ hZX
    simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
    rcases hZ with rfl | rfl
    · exact absurd rfl hZX
    · exact hY
  · rw [Finset.erase_insert (by simpa using hXY)]
    simp

/-- **Potential bound.** If every equation consists of two variables whose potentials differ
by at most one, the initial facts with value `0` have potential `0` and those with value `1`
have potential at least `D`, then after `r` rounds every fact `X = 0` has potential at most
`r` and every fact `X = 1` has potential at least `D - r`. -/
theorem known_potential (Φ : V → ℕ) (D : ℕ)
    (heq : ∀ h ∈ P.equations, ∃ X Y, X ≠ Y ∧ h = {X, Y} ∧ Φ X ≤ Φ Y + 1 ∧ Φ Y ≤ Φ X + 1)
    (hinit : ∀ f ∈ P.initial, (f.2 = 0 ∧ Φ f.1 = 0) ∨ (f.2 = 1 ∧ D ≤ Φ f.1)) :
    ∀ r, ∀ f ∈ P.known r, (f.2 = 0 ∧ Φ f.1 ≤ r) ∨ (f.2 = 1 ∧ D ≤ Φ f.1 + r) := by
  intro r
  induction r with
  | zero =>
    intro f hf
    rcases hinit f hf with h | h
    · exact Or.inl ⟨h.1, by omega⟩
    · exact Or.inr ⟨h.1, by omega⟩
  | succ r ih =>
    intro f hf
    rcases hf with hf | ⟨h, hh, hfh, b, hb, hsum⟩
    · rcases ih f hf with h | h
      · exact Or.inl ⟨h.1, by omega⟩
      · exact Or.inr ⟨h.1, by omega⟩
    · obtain ⟨X, Y, hXY, rfl, h1, h2⟩ := heq h hh
      -- the fact concerns one of the two variables; the other one is known
      have key : ∀ A B : V, A ≠ B → Φ A ≤ Φ B + 1 → Φ B ≤ Φ A + 1 →
          f.1 = A → ({A, B} : Finset V) = {X, Y} →
          (f.2 = 0 ∧ Φ f.1 ≤ r + 1) ∨ (f.2 = 1 ∧ D ≤ Φ f.1 + (r + 1)) := by
        intro A B hAB hA hB hfA hAB'
        have hBmem : B ∈ ({X, Y} : Finset V) := by rw [← hAB']; simp
        have hBk := hb B hBmem (by rw [hfA]; exact Ne.symm hAB)
        have hf2 : f.2 = b B := by
          rw [hsum, hfA, ← hAB', Finset.erase_insert (by simpa using hAB)]
          simp
        rcases ih _ hBk with h' | h'
        · exact Or.inl ⟨hf2.trans h'.1, by rw [hfA]; dsimp at h'; omega⟩
        · exact Or.inr ⟨hf2.trans h'.1, by rw [hfA]; dsimp at h'; omega⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hfh
      rcases hfh with hfX | hfY
      · exact key X Y hXY h1 h2 hfX rfl
      · exact key Y X (Ne.symm hXY) h2 h1 hfY (Finset.pair_comm _ _)

theorem conflict_bound (Φ : V → ℕ) (D : ℕ)
    (heq : ∀ h ∈ P.equations, ∃ X Y, X ≠ Y ∧ h = {X, Y} ∧ Φ X ≤ Φ Y + 1 ∧ Φ Y ≤ Φ X + 1)
    (hinit : ∀ f ∈ P.initial, (f.2 = 0 ∧ Φ f.1 = 0) ∨ (f.2 = 1 ∧ D ≤ Φ f.1))
    {r : ℕ} (hc : P.HasConflict r) : D ≤ 2 * r := by
  obtain ⟨X, h0, h1⟩ := hc
  rcases known_potential P Φ D heq hinit r _ h0 with h | h
  · rcases known_potential P Φ D heq hinit r _ h1 with h' | h'
    · exact absurd h'.1 (by simp)
    · dsimp at h h'; omega
  · exact absurd h.1 (by simp)

open Classical in
theorem conflictRound_eq_find (h : ∃ r, P.HasConflict r) :
    P.conflictRound = (Nat.find h : ℕ∞) := by
  classical
  unfold ParitySystem.conflictRound
  apply le_antisymm
  · exact iInf₂_le (Nat.find h) (Nat.find_spec h)
  · exact le_iInf₂ fun r hr => by exact_mod_cast Nat.find_min' h hr

end Lax119563Proofs.Counter

end Counter_Propagation

/-! ### Formerly `Lax119563Proofs.Counter.Stabilize` -/

section Counter_Stabilize

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

end Counter_Stabilize

/-! ### Formerly `Lax119563Proofs.Counter.System` -/

section Counter_System

/-!
# The counter implicit parity system

Locations (with `m = ℓ K` data positions): the main location `0` with the full coordinate
domain, the endpoint locations `1` (initialized `0`, domain `supp 0`) and `2` (initialized
`1`, domain `supp t`), and for every data position `j < m` the private locations
`p_j = 3 + 2j` and `q_j = 4 + 2j` with domain `𝔠'_j`. The schemas are
`X_{1,a} = X_{0,a}`, `X_{2,a} = X_{0,a}` and, for every `j`,
`X_{0,a} = X_{p_j,a} = X_{q_j,a} = X_{0,a+δ_j}` for the addresses `a` supported in `𝔠'_j`,
which are exactly the addresses with data prefix `1^j 0`.
-/

open Lax119563.ImplicitParitySystems

namespace Lax119563Proofs.Counter

variable {K ℓ : ℕ}

/-- The coordinates allowed for the increment at position `j`: data coordinates have the bits
of a `1^j 0` prefix at the data positions `≤ j` of their block, and the checksum coordinate
has bit `K` in every row lying entirely below `j`. -/
def GoodCoord (K ℓ j : ℕ) (c : Coord (K + 1) ℓ) : Prop :=
  (∀ p : Fin (ℓ * K), (p : ℕ) ≤ j → Fin.castSucc ((pos K ℓ).symm p).2 = c.1 →
      c.2 ((pos K ℓ).symm p).1 = if (p : ℕ) < j then 1 else 0) ∧
    (c.1 = Fin.last K → ∀ t : Fin ℓ, K * ((t : ℕ) + 1) ≤ j → c.2 t = (K : ZMod 2))

open Classical in
/-- The coordinate domain `𝔠'_j`. -/
noncomputable def dom (K ℓ j : ℕ) : Finset (Coord (K + 1) ℓ) :=
  Finset.univ.filter (GoodCoord K ℓ j)

theorem mem_dom {j : ℕ} {c : Coord (K + 1) ℓ} : c ∈ dom K ℓ j ↔ GoodCoord K ℓ j c := by
  simp [dom]

theorem supp_subset_iff (a : Arr K ℓ) (D : Finset (Coord (K + 1) ℓ)) :
    supp a ⊆ D ↔ ∀ i, (i, a i) ∈ D := by
  simp [supp, Finset.image_subset_iff]

theorem eq_of_supp_subset {a c : Arr K ℓ} (h : supp a ⊆ supp c) : a = c := by
  rw [supp_subset_iff] at h
  funext i
  have := h i
  simp only [supp, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq] at this
  obtain ⟨i', rfl, h'⟩ := this
  exact h'.symm

/-- The addresses supported in `𝔠'_j` are those with data prefix `1^j 0`. -/
theorem supp_subset_dom_iff {j : ℕ} {a : Arr K ℓ} (ha : IsAddress a) :
    supp a ⊆ dom K ℓ j ↔ Prefix j a := by
  rw [supp_subset_iff]
  constructor
  · intro h p hp
    have := (mem_dom.mp (h (Fin.castSucc ((pos K ℓ).symm p).2))).1 p hp rfl
    exact this
  · intro h i
    refine mem_dom.mpr ⟨?_, ?_⟩
    · intro p hp hi
      dsimp only at hi ⊢
      rw [← hi]
      exact h p hp
    · intro hi t ht
      dsimp only at hi ⊢
      rw [hi, last_eq_of_isAddress ha]
      have : ∀ i' : Fin K, a (Fin.castSucc i') t = 1 := by
        intro i'
        rw [← dbit_pos a t i', h _ (by rw [pos_val]; dsimp; nlinarith [i'.2]),
          if_pos (by rw [pos_val]; dsimp; nlinarith [i'.2])]
      simp [Finset.sum_apply, this]

end Lax119563Proofs.Counter

end Counter_System

/-! ### Formerly `Lax119563Proofs.Counter.Construction` -/

section Counter_Construction

/-!
# The counter as an implicit parity system

See `System.lean` for the layout of locations and schemas.
-/

open Lax119563.ImplicitParitySystems

namespace Lax119563Proofs.Counter

variable {K ℓ : ℕ}

/-- The number `3 + 2m` of locations. -/
abbrev numLoc (K ℓ : ℕ) : ℕ := 3 + 2 * (ℓ * K)

open Classical in
/-- The coordinate domain of location `n`. -/
noncomputable def domN (K ℓ n : ℕ) : Finset (Coord (K + 1) ℓ) :=
  if n = 0 then Finset.univ
  else if n = 1 then supp (0 : Arr K ℓ)
  else if n = 2 then supp (top K ℓ)
  else dom K ℓ ((n - 3) / 2)

theorem domN_p (j : ℕ) : domN K ℓ (3 + 2 * j) = dom K ℓ j := by
  rw [domN, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1
  omega

theorem domN_q (j : ℕ) : domN K ℓ (4 + 2 * j) = dom K ℓ j := by
  rw [domN, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1
  omega

/-- The main location. -/
def locMain : Fin (numLoc K ℓ) := ⟨0, by unfold numLoc; omega⟩
/-- The endpoint location initialized `0`. -/
def locZ0 : Fin (numLoc K ℓ) := ⟨1, by unfold numLoc; omega⟩
/-- The endpoint location initialized `1`. -/
def locZ1 : Fin (numLoc K ℓ) := ⟨2, by unfold numLoc; omega⟩
/-- The first private location of the increment at `j`. -/
def locP (j : Fin (ℓ * K)) : Fin (numLoc K ℓ) := ⟨3 + 2 * j, by unfold numLoc; omega⟩
/-- The second private location of the increment at `j`. -/
def locQ (j : Fin (ℓ * K)) : Fin (numLoc K ℓ) := ⟨4 + 2 * j, by unfold numLoc; omega⟩

/-- The identity block-induced permutation. -/
def idPerm : BlockPerm (K + 1) ℓ := ⟨1, 0, by simp⟩

/-- The increment `a ↦ a + δ_j`. -/
def incPerm (j : ℕ) : BlockPerm (K + 1) ℓ := ⟨1, shift K ℓ j, sum_shift j⟩

theorem idPerm_apply (c : Coord (K + 1) ℓ) : (idPerm : BlockPerm (K + 1) ℓ).apply c = c := by
  simp [idPerm, BlockPerm.apply]

theorem idPerm_act (a : Arr K ℓ) : (idPerm : BlockPerm (K + 1) ℓ).act a = a := by
  funext i
  simp [idPerm, BlockPerm.act]; rfl

theorem incPerm_act (j : ℕ) (a : Arr K ℓ) : (incPerm (K := K) (ℓ := ℓ) j).act a = a + shift K ℓ j := by
  funext i
  simp [incPerm, BlockPerm.act]; rfl

theorem image_idPerm (D : Finset (Coord (K + 1) ℓ)) :
    D.image (idPerm : BlockPerm (K + 1) ℓ).apply = D := by
  have : (idPerm : BlockPerm (K + 1) ℓ).apply = id := funext idPerm_apply
  rw [this, Finset.image_id]

/-- Indices of the schemas: the two endpoint schemas, and three schemas per increment. -/
abbrev SchIdx (K ℓ : ℕ) := Bool ⊕ (Fin (ℓ * K) × Fin 3)

/-- The schemas of the counter. -/
noncomputable def schemaOf : SchIdx K ℓ → Schema (K + 1) ℓ (numLoc K ℓ)
  | .inl false => .binary locZ0 locMain (supp 0) idPerm idPerm
  | .inl true => .binary locZ1 locMain (supp (top K ℓ)) idPerm idPerm
  | .inr (j, c) =>
    if c = 0 then .binary locMain (locP j) (dom K ℓ j) idPerm idPerm
    else if c = 1 then .binary (locP j) (locQ j) (dom K ℓ j) idPerm idPerm
    else .binary (locQ j) locMain (dom K ℓ j) idPerm (incPerm j)

/-- The two location values of each schema. -/
def locPair : SchIdx K ℓ → ℕ × ℕ
  | .inl false => (1, 0)
  | .inl true => (2, 0)
  | .inr (j, c) =>
    if c = 0 then (0, 3 + 2 * j) else if c = 1 then (3 + 2 * j, 4 + 2 * j) else (4 + 2 * j, 0)

theorem schemaOf_eq (x : SchIdx K ℓ) : ∃ (u v : Fin (numLoc K ℓ)) (D : Finset (Coord (K + 1) ℓ))
    (σ τ : BlockPerm (K + 1) ℓ), schemaOf x = .binary u v D σ τ ∧
      ((u : ℕ), (v : ℕ)) = locPair x := by
  rcases x with (_ | _) | ⟨j, c⟩
  · exact ⟨_, _, _, _, _, rfl, rfl⟩
  · exact ⟨_, _, _, _, _, rfl, rfl⟩
  · fin_cases c
    · exact ⟨_, _, _, _, _, rfl, rfl⟩
    · exact ⟨_, _, _, _, _, rfl, rfl⟩
    · exact ⟨_, _, _, _, _, rfl, rfl⟩

theorem locPair_ne (x : SchIdx K ℓ) : (locPair x).1 ≠ (locPair x).2 := by
  rcases x with (_ | _) | ⟨j, c⟩
  · simp [locPair]
  · simp [locPair]
  · fin_cases c <;> simp [locPair] <;> omega

theorem locPair_inj {x y : SchIdx K ℓ} (h : ({(locPair x).1, (locPair x).2} : Finset ℕ) =
    {(locPair y).1, (locPair y).2}) : x = y := by
  have h1 : (locPair x).1 ∈ ({(locPair y).1, (locPair y).2} : Finset ℕ) := h ▸ by simp
  have h2 : (locPair x).2 ∈ ({(locPair y).1, (locPair y).2} : Finset ℕ) := h ▸ by simp
  have h3 : (locPair y).1 ∈ ({(locPair x).1, (locPair x).2} : Finset ℕ) := h.symm ▸ by simp
  have h4 : (locPair y).2 ∈ ({(locPair x).1, (locPair x).2} : Finset ℕ) := h.symm ▸ by simp
  clear h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 h3 h4
  rcases x with b | ⟨j, c⟩ <;> rcases y with b' | ⟨j', c'⟩
  · cases b <;> cases b' <;> first | rfl | (simp [locPair] at h1 h2 h3 h4)
  · exfalso
    cases b <;> fin_cases c' <;> simp [locPair] at h1 h2 h3 h4 <;> omega
  · exfalso
    cases b' <;> fin_cases c <;> simp [locPair] at h1 h2 h3 h4 <;> omega
  · fin_cases c <;> fin_cases c' <;> simp [locPair] at h1 h2 h3 h4 ⊢ <;>
      first | (exfalso; omega) | (apply Fin.ext; omega)

theorem two_card_inter {α : Type*} [DecidableEq α] {s t : Finset α} (hs : s.card = 2)
    (ht : t.card = 2) (hne : s ≠ t) : (s ∩ t).card ≤ 1 := by
  by_contra h
  push Not at h
  have e1 : s ∩ t = s := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have e2 : s ∩ t = t := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  exact hne (e1.symm.trans e2)

theorem locations_schemaOf (x : SchIdx K ℓ) : ∃ u v : Fin (numLoc K ℓ),
    (schemaOf x).locations = {u, v} ∧ ((u : ℕ), (v : ℕ)) = locPair x := by
  obtain ⟨u, v, D, σ, τ, h, hp⟩ := schemaOf_eq x
  exact ⟨u, v, by rw [h]; rfl, hp⟩

theorem schemas_meet_aux : ((Finset.univ : Finset (SchIdx K ℓ)).toList.map schemaOf).Pairwise
    fun e e' => (e.locations ∩ e'.locations).card ≤ 1 := by
  rw [List.pairwise_map]
  refine (Finset.nodup_toList _).pairwise_of_forall_ne fun x _ y _ hxy => ?_
  obtain ⟨u, v, hl, hp⟩ := locations_schemaOf x
  obtain ⟨u', v', hl', hp'⟩ := locations_schemaOf y
  rw [hl, hl']
  have hne := locPair_ne x
  have hne' := locPair_ne y
  rw [← hp] at hne
  rw [← hp'] at hne'
  have huv : u ≠ v := fun h => hne (by simp [h])
  have huv' : u' ≠ v' := fun h => hne' (by simp [h])
  refine two_card_inter (Finset.card_pair huv) (Finset.card_pair huv') fun h => hxy (locPair_inj ?_)
  have := congrArg (Finset.image Fin.val) h
  simp only [Finset.image_insert, Finset.image_singleton] at this
  rw [← hp, ← hp']
  exact this

theorem schemaOf_wellFormed (x : SchIdx K ℓ) :
    (schemaOf x).WellFormed (fun v => domN K ℓ v) := by
  rcases x with b | ⟨j, c⟩
  · cases b
    · refine ⟨by simp [locZ0, locMain, Fin.ext_iff], ?_, ?_⟩ <;>
        simp [image_idPerm, domN, locZ0, locMain]
    · refine ⟨by simp [locZ1, locMain, Fin.ext_iff], ?_, ?_⟩ <;>
        simp [image_idPerm, domN, locZ1, locMain]
  · fin_cases c
    · refine ⟨by simp [locMain, locP, Fin.ext_iff] <;> omega, ?_, ?_⟩
      · simp [image_idPerm, domN, locMain]
      · show (dom K ℓ j).image idPerm.apply ⊆ domN K ℓ (3 + 2 * j)
        rw [image_idPerm, domN_p]
    · refine ⟨by simp [locQ, locP, Fin.ext_iff] <;> omega, ?_, ?_⟩
      · show (dom K ℓ j).image idPerm.apply ⊆ domN K ℓ (3 + 2 * j)
        rw [image_idPerm, domN_p]
      · show (dom K ℓ j).image idPerm.apply ⊆ domN K ℓ (4 + 2 * j)
        rw [image_idPerm, domN_q]
    · refine ⟨by simp [locQ, locMain, Fin.ext_iff] <;> omega, ?_, ?_⟩
      · show (dom K ℓ j).image idPerm.apply ⊆ domN K ℓ (4 + 2 * j)
        rw [image_idPerm, domN_q]
      · show _ ⊆ domN K ℓ 0
        simp [domN]

end Lax119563Proofs.Counter

end Counter_Construction

/-! ### Formerly `Lax119563Proofs.Counter.Rounds` -/

section Counter_Rounds

/-!
# The conflict round of the counter

Unit propagation on the counter has a conflict, and its conflict round is at least `2^m`
for `m = ℓ K`:

* *Lower bound.* The potential `Φ(X_{v,a}) = 3 val(a) + 1` at the main location (with
  `+2`, `+3` at the private locations, `0` at `z₀` and `3 val(t) + 2` at `z₁`) changes by at
  most one along every equation, so `0`s spread up and `1`s spread down by one per round.
* *Finiteness.* Every address eventually receives the value `0` at the main location, by
  induction on its counter value: decrementing at the first one bit gives an address with
  data prefix `1^j 0`, from which the increment schemas propagate in three rounds.
-/

open Lax119563.ImplicitParitySystems Lax119563.ParitySystems

namespace Lax119563Proofs.Counter

variable {K ℓ : ℕ}

/-- The counter implicit parity system `𝓘_ctr^{K+1,ℓ}`. -/
noncomputable def counter (K ℓ : ℕ) : ImplicitParitySystem (K + 1) ℓ where
  numLocations := numLoc K ℓ
  domain v := domN K ℓ v
  schemas := (Finset.univ : Finset (SchIdx K ℓ)).toList.map schemaOf
  init v := if (v : ℕ) = 1 then some 0 else if (v : ℕ) = 2 then some 1 else none
  schema_wellFormed := by
    intro e he
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp he
    exact schemaOf_wellFormed x
  schemas_meet := schemas_meet_aux

/-- The parity system of the counter. -/
noncomputable abbrev ctrP (K ℓ : ℕ) := (counter K ℓ).toParitySystem

theorem schemaOf_mem (x : SchIdx K ℓ) : schemaOf x ∈ (counter K ℓ).schemas :=
  List.mem_map.mpr ⟨x, Finset.mem_toList.mpr (Finset.mem_univ x), rfl⟩

theorem equation_mem (x : SchIdx K ℓ) {a : Arr K ℓ} (ha : IsAddress a)
    (hs : supp a ⊆ (schemaOf x).domain) : (schemaOf x).equation a ∈ (ctrP K ℓ).equations :=
  ⟨schemaOf x, schemaOf_mem x, a, ha, hs, rfl⟩

/-! ### The lower bound -/

/-- The potential of a variable. -/
def pot (K ℓ : ℕ) (X : Fin (numLoc K ℓ) × Arr K ℓ) : ℕ :=
  if (X.1 : ℕ) = 0 then 3 * val X.2 + 1
  else if (X.1 : ℕ) = 1 then 0
  else if (X.1 : ℕ) = 2 then 3 * val (top K ℓ) + 2
  else if (X.1 : ℕ) % 2 = 1 then 3 * val X.2 + 2
  else 3 * val X.2 + 3

theorem pot_main (a : Arr K ℓ) : pot K ℓ (locMain, a) = 3 * val a + 1 := by
  simp [pot, locMain]

theorem pot_z0 (a : Arr K ℓ) : pot K ℓ (locZ0, a) = 0 := by
  simp [pot, locZ0]

theorem pot_z1 (a : Arr K ℓ) : pot K ℓ (locZ1, a) = 3 * val (top K ℓ) + 2 := by
  simp [pot, locZ1]

theorem pot_p (j : Fin (ℓ * K)) (a : Arr K ℓ) : pot K ℓ (locP j, a) = 3 * val a + 2 := by
  unfold pot
  have h : ((locP j, a).1 : ℕ) = 3 + 2 * (j : ℕ) := rfl
  have h' : (locP j, a).2 = a := rfl
  rw [h, h']
  split_ifs <;> omega

theorem pot_q (j : Fin (ℓ * K)) (a : Arr K ℓ) : pot K ℓ (locQ j, a) = 3 * val a + 3 := by
  unfold pot
  have h : ((locQ j, a).1 : ℕ) = 4 + 2 * (j : ℕ) := rfl
  have h' : (locQ j, a).2 = a := rfl
  rw [h, h']
  split_ifs <;> omega

theorem ne_of_val {X Y : Fin (numLoc K ℓ) × Arr K ℓ} (h : (X.1 : ℕ) ≠ (Y.1 : ℕ)) : X ≠ Y :=
  fun e => h (by rw [e])

theorem eqn_start (a : Arr K ℓ) :
    (schemaOf (K := K) (ℓ := ℓ) (.inl false)).equation a = {(locZ0, a), (locMain, a)} := by
  simp [schemaOf, Schema.equation, idPerm_act]

theorem eqn_stop (a : Arr K ℓ) :
    (schemaOf (K := K) (ℓ := ℓ) (.inl true)).equation a = {(locZ1, a), (locMain, a)} := by
  simp [schemaOf, Schema.equation, idPerm_act]

theorem eqn_up (j : Fin (ℓ * K)) (a : Arr K ℓ) :
    (schemaOf (K := K) (ℓ := ℓ) (.inr (j, 0))).equation a = {(locMain, a), (locP j, a)} := by
  simp [schemaOf, Schema.equation, idPerm_act]

theorem eqn_mid (j : Fin (ℓ * K)) (a : Arr K ℓ) :
    (schemaOf (K := K) (ℓ := ℓ) (.inr (j, 1))).equation a = {(locP j, a), (locQ j, a)} := by
  simp [schemaOf, Schema.equation, idPerm_act]

theorem eqn_down (j : Fin (ℓ * K)) (a : Arr K ℓ) :
    (schemaOf (K := K) (ℓ := ℓ) (.inr (j, 2))).equation a =
      {(locQ j, a), (locMain, a + shift K ℓ j)} := by
  simp [schemaOf, Schema.equation, idPerm_act, incPerm_act]

theorem pot_equations : ∀ h ∈ (ctrP K ℓ).equations, ∃ X Y : Fin (numLoc K ℓ) × Arr K ℓ, X ≠ Y ∧ h = {X, Y} ∧
    pot K ℓ X ≤ pot K ℓ Y + 1 ∧ pot K ℓ Y ≤ pot K ℓ X + 1 := by
  rintro h ⟨e, he, a, ha, hs, rfl⟩
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp he
  rcases x with (_ | _) | ⟨j, c⟩
  · have hs' : supp a ⊆ supp (0 : Arr K ℓ) := hs
    obtain rfl := eq_of_supp_subset hs'
    refine ⟨(locZ0, 0), (locMain, 0), ne_of_val (by show 1 ≠ 0; omega), eqn_start 0, ?_, ?_⟩
    · rw [pot_z0, pot_main, val_zero] <;> omega
    · rw [pot_z0, pot_main, val_zero] <;> omega
  · have hs' : supp a ⊆ supp (top K ℓ) := hs
    obtain rfl := eq_of_supp_subset hs'
    refine ⟨(locZ1, top K ℓ), (locMain, top K ℓ), ne_of_val (by show 2 ≠ 0; omega),
      eqn_stop _, ?_, ?_⟩
    · rw [pot_z1, pot_main] <;> omega
    · rw [pot_z1, pot_main] <;> omega
  · fin_cases c
    · refine ⟨(locMain, a), (locP j, a), ne_of_val (by show 0 ≠ 3 + 2 * (j : ℕ); omega),
        eqn_up j a, ?_, ?_⟩
      · rw [pot_p, pot_main] <;> omega
      · rw [pot_p, pot_main] <;> omega
    · refine ⟨(locP j, a), (locQ j, a), ne_of_val (by show 3 + 2 * (j : ℕ) ≠ 4 + 2 * j; omega),
        eqn_mid j a, ?_, ?_⟩
      · rw [pot_p, pot_q] <;> omega
      · rw [pot_p, pot_q] <;> omega
    · have hs' : supp a ⊆ dom K ℓ j := hs
      have hpre := (supp_subset_dom_iff ha).mp hs'
      have hv := val_add_shift j.2 hpre
      refine ⟨(locQ j, a), (locMain, a + shift K ℓ j),
        ne_of_val (by show 4 + 2 * (j : ℕ) ≠ 0; omega), eqn_down j a, ?_, ?_⟩
      · rw [pot_q, pot_main, hv] <;> omega
      · rw [pot_q, pot_main, hv] <;> omega

theorem pot_initial : ∀ f ∈ (ctrP K ℓ).initial,
    (f.2 = 0 ∧ pot K ℓ f.1 = 0) ∨ (f.2 = 1 ∧ 3 * val (top K ℓ) + 2 ≤ pot K ℓ f.1) := by
  rintro ⟨⟨v, a⟩, b⟩ ⟨b', hb', hbb, -, -⟩
  dsimp only at hbb
  subst hbb
  change (if (v : ℕ) = 1 then some 0 else if (v : ℕ) = 2 then some 1 else none) = some b at hb'
  split_ifs at hb' with h1 h2
  · cases hb'
    left
    exact ⟨rfl, by simp [pot, h1]⟩
  · cases hb'
    right
    exact ⟨rfl, by simp [pot, h2]⟩

/-- **Lower bound.** A conflict in round `r` needs `3 val(t) + 2 ≤ 2 r`. -/
theorem conflict_lower {r : ℕ} (hc : (ctrP K ℓ).HasConflict r) :
    3 * val (top K ℓ) + 2 ≤ 2 * r :=
  conflict_bound _ (pot K ℓ) _ pot_equations pot_initial hc

/-! ### A conflict occurs -/

theorem shift_add_shift (j : ℕ) : shift K ℓ j + shift K ℓ j = 0 := by
  funext i
  exact blockCoord_add_self _

theorem main_zero_known (n : ℕ) : ∀ a : Arr K ℓ, IsAddress a → val a = n →
    ∃ r, ((locMain, a), (0 : ZMod 2)) ∈ (ctrP K ℓ).known r := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a ha hn
  by_cases hz : ∀ p, dbit a p = 0
  · obtain rfl := eq_zero_of_dbit ha hz
    refine ⟨1, known_succ_of_pair _ (Y := (locZ0, 0)) (ne_of_val (by show 0 ≠ 1; omega)) ?_ ?_⟩
    · have := equation_mem (K := K) (ℓ := ℓ) (.inl false) (a := 0)
        (by simp [IsAddress]) (subset_refl _)
      rw [eqn_start, Finset.pair_comm] at this
      exact this
    · refine ⟨0, ?_, rfl, by simp [IsAddress], ?_⟩
      · simp [counter, locZ0]
      · show supp 0 ⊆ domN K ℓ 1
        simp [domN]
  · push Not at hz
    have hex : ∃ p : ℕ, ∃ hp : p < ℓ * K, dbit a ⟨p, hp⟩ ≠ 0 := by
      obtain ⟨p, hp⟩ := hz
      exact ⟨p, p.2, hp⟩
    classical
    set j := Nat.find hex with hjdef
    obtain ⟨hj, hj1⟩ := Nat.find_spec hex
    have hlow : ∀ p : Fin (ℓ * K), (p : ℕ) < j → dbit a p = 0 := by
      intro p hp
      by_contra hne
      exact Nat.find_min hex hp ⟨p.2, hne⟩
    set a' := a + shift K ℓ j with ha'def
    have ha' : IsAddress a' := isAddress_add ha (isAddress_shift j)
    have hpre : Prefix j a' := by
      intro p hp
      rw [dbit_add, dbit_shift, if_pos hp]
      rcases Nat.lt_or_eq_of_le hp with hlt | heq
      · rw [hlow p hlt, if_pos hlt]; decide
      · have : p = ⟨j, hj⟩ := Fin.ext heq
        subst this
        rw [zmod2_eq_one_of_ne_zero hj1, if_neg (lt_irrefl _)]; decide
    have hback : a' + shift K ℓ j = a := by
      rw [ha'def, add_assoc, shift_add_shift, add_zero]
    have hval := val_add_shift hj hpre
    rw [hback] at hval
    obtain ⟨r, hr⟩ := ih (val a') (by omega) a' ha' rfl
    have hsupp : supp a' ⊆ dom K ℓ j := (supp_subset_dom_iff ha').mpr hpre
    let jj : Fin (ℓ * K) := ⟨j, hj⟩
    have e0 := equation_mem (K := K) (ℓ := ℓ) (.inr (jj, 0)) ha' hsupp
    have e1 := equation_mem (K := K) (ℓ := ℓ) (.inr (jj, 1)) ha' hsupp
    have e2 := equation_mem (K := K) (ℓ := ℓ) (.inr (jj, 2)) ha' hsupp
    rw [eqn_up, Finset.pair_comm] at e0
    rw [eqn_mid, Finset.pair_comm] at e1
    rw [eqn_down, Finset.pair_comm] at e2
    have k1 : ((locP jj, a'), (0 : ZMod 2)) ∈ (ctrP K ℓ).known (r + 1) :=
      known_succ_of_pair _ (ne_of_val (by show 3 + 2 * j ≠ 0; omega)) e0 hr
    have k2 : ((locQ jj, a'), (0 : ZMod 2)) ∈ (ctrP K ℓ).known (r + 1 + 1) :=
      known_succ_of_pair _ (ne_of_val (by show 4 + 2 * j ≠ 3 + 2 * j; omega)) e1 k1
    have k3 := known_succ_of_pair _ (X := (locMain, a' + shift K ℓ j))
      (ne_of_val (by show 0 ≠ 4 + 2 * j; omega)) e2 k2
    rw [hback] at k3
    exact ⟨_, k3⟩

theorem exists_conflict : ∃ r, (ctrP K ℓ).HasConflict r := by
  obtain ⟨r, hr⟩ := main_zero_known (K := K) (ℓ := ℓ) _ (top K ℓ) isAddress_top rfl
  have e := equation_mem (K := K) (ℓ := ℓ) (.inl true) isAddress_top (subset_refl _)
  rw [eqn_stop] at e
  refine ⟨r + 1, (locZ1, top K ℓ),
    known_succ_of_pair _ (ne_of_val (by show 2 ≠ 0; omega)) e hr, ?_⟩
  · refine known_mono _ (Nat.zero_le _) ⟨1, ?_, rfl, isAddress_top, ?_⟩
    · simp [counter, locZ1]
    · show supp (top K ℓ) ⊆ domN K ℓ 2
      simp [domN]

/-- **The conflict round of the counter.** It is finite and at least `2^{ℓ K}`. -/
theorem counter_conflictRound : ∃ τ : ℕ, (counter K ℓ).conflictRound = τ ∧ 2 ^ (ℓ * K) ≤ τ := by
  classical
  refine ⟨Nat.find exists_conflict, conflictRound_eq_find _ exists_conflict, ?_⟩
  have h1 := conflict_lower (Nat.find_spec (exists_conflict (K := K) (ℓ := ℓ)))
  have h2 := val_top (K := K) (ℓ := ℓ)
  have h3 : 1 ≤ 2 ^ (ℓ * K) := Nat.one_le_two_pow
  omega

end Lax119563Proofs.Counter

end Counter_Rounds

/-! ### Formerly `Lax119563Proofs.Counter.Size` -/

section Counter_Size

/-!
# The size parameter of the counter

For the increment at position `j`, all coordinates of `𝔠'_j` have fixed bits in the rows
`t < ⌊j / K⌋`. Hence `|𝔠'_j| ≤ (K+1) 2^{ℓ - ⌊j/K⌋}`, and the columns of the check matrix
indexed by `𝔠'_j` lie in the span of `K + 1` block vectors and `ℓ - ⌊j/K⌋` unit vectors,
so `rank B_e ≤ K + 1 + ℓ - ⌊j/K⌋`. Summing the geometric series over the rows gives
`rowSpaceSize = O_K(2^ℓ)`.
-/

open Lax119563.ImplicitParitySystems Lax119563.RowSpaceCompiler
open Lax119563.MatrixCompiler (checkMatrix)

namespace Lax119563Proofs.Counter

variable {K ℓ : ℕ}

/-- The fixed bit value of block `i` in a row lying entirely below the increment position. -/
def fixBit (K : ℕ) (i : Fin (K + 1)) : ZMod 2 := if i = Fin.last K then (K : ZMod 2) else 1

/-- All coordinates of `D` have the fixed bits in the rows `t < r`. -/
def FixedRows (r : ℕ) (D : Finset (Coord (K + 1) ℓ)) : Prop :=
  ∀ c ∈ D, ∀ t : Fin ℓ, (t : ℕ) < r → c.2 t = fixBit K c.1

theorem fixedRows_zero (D : Finset (Coord (K + 1) ℓ)) : FixedRows 0 D :=
  fun _ _ _ ht => absurd ht (Nat.not_lt_zero _)

theorem fixedRows_dom (j : ℕ) : FixedRows (j / K) (dom K ℓ j) := by
  rintro ⟨i, b⟩ hc t ht
  have hg := mem_dom.mp hc
  have hKt : K * ((t : ℕ) + 1) ≤ j :=
    (Nat.mul_le_mul_left K (Nat.succ_le_of_lt ht)).trans (Nat.mul_div_le j K)
  induction i using Fin.lastCases with
  | last =>
    simp only [fixBit]
    exact hg.2 rfl t hKt
  | cast i =>
    simp only [fixBit, if_neg (Fin.castSucc_lt_last i).ne]
    have hlt : (pos K ℓ (t, i) : ℕ) < j := by
      rw [pos_val]; dsimp
      have := i.2
      nlinarith
    have := hg.1 (pos K ℓ (t, i)) hlt.le (by simp)
    simpa [hlt] using this

theorem card_fixed_le (r : ℕ) (z : ZMod 2) :
    (Finset.univ.filter fun b : BlockCoord ℓ => ∀ t : Fin ℓ, (t : ℕ) < r → b t = z).card ≤
      2 ^ (ℓ - r) := by
  have : (Finset.univ : Finset (Fin (ℓ - r) → ZMod 2)).card = 2 ^ (ℓ - r) := by
    simp [Finset.card_univ, ZMod.card]
  rw [← this]
  refine Finset.card_le_card_of_injOn (fun b u => b ⟨r + u, by omega⟩)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_
  intro b hb b' hb' h
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hb hb'
  funext t
  by_cases ht : (t : ℕ) < r
  · rw [hb t ht, hb' t ht]
  · have := congrFun h ⟨t - r, by omega⟩
    simp only at this
    have e : (⟨r + (t - r), by omega⟩ : Fin ℓ) = t := Fin.ext (by simp; omega)
    rwa [e] at this

theorem card_le_of_fixedRows {r : ℕ} {D : Finset (Coord (K + 1) ℓ)} (hD : FixedRows r D) :
    D.card ≤ (K + 1) * 2 ^ (ℓ - r) := by
  classical
  have hsub : D ⊆ Finset.univ.biUnion fun i : Fin (K + 1) =>
      (Finset.univ.filter fun b : BlockCoord ℓ => ∀ t : Fin ℓ, (t : ℕ) < r → b t = fixBit K i).image
        fun b => (i, b) := by
    rintro ⟨i, b⟩ hc
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_filter, Prod.mk.injEq]
    exact ⟨i, b, fun t ht => hD _ hc t ht, rfl, rfl⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  calc ∑ i : Fin (K + 1), _ ≤ ∑ _i : Fin (K + 1), 2 ^ (ℓ - r) :=
        Finset.sum_le_sum fun i _ => Finset.card_image_le.trans (card_fixed_le r _)
    _ = (K + 1) * 2 ^ (ℓ - r) := by simp

theorem card_filter_ge (r : ℕ) :
    (Finset.univ.filter fun t : Fin ℓ => r ≤ (t : ℕ)).card ≤ ℓ - r := by
  have : (Finset.Ico r ℓ).card = ℓ - r := Nat.card_Ico r ℓ
  rw [← this]
  refine Finset.card_le_card_of_injOn (fun t => (t : ℕ)) ?_ (fun a _ b _ h => Fin.ext h)
  intro t ht
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht
  simp [ht, t.2]

/-- The block coordinate with the fixed bits of block `i` in the rows `t < r` and zeros
elsewhere. -/
def fixT (K ℓ r : ℕ) (i : Fin (K + 1)) : BlockCoord ℓ :=
  fun t => if (t : ℕ) < r then fixBit K i else 0

/-- A column of the check matrix splits into the column of `fixT` and unit vectors of the
free rows. -/
theorem col_decomp (r : ℕ) (x : Coord (K + 1) ℓ)
    (hb : ∀ t : Fin ℓ, (t : ℕ) < r → x.2 t = fixBit K x.1) :
    (fun row => checkMatrix (K + 1) ℓ row x) =
      (fun row => checkMatrix (K + 1) ℓ row (x.1, fixT K ℓ r x.1)) +
        ∑ t ∈ Finset.univ.filter (fun t : Fin ℓ => r ≤ (t : ℕ)),
          x.2 t • (Pi.single (Sum.inr t) (1 : ZMod 2) : Fin (K + 1 - 1) ⊕ Fin ℓ → ZMod 2) := by
  obtain ⟨i, b⟩ := x
  funext row
  rw [Pi.add_apply, Finset.sum_apply]
  rcases row with i₀ | t₀
  · simp [checkMatrix]
  · simp only [checkMatrix, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      Sum.inr.injEq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_filter, Finset.mem_univ, true_and, fixT]
    by_cases ht : (t₀ : ℕ) < r
    · rw [if_pos ht, if_neg (by omega), add_zero]
      exact hb t₀ ht
    · rw [if_neg ht, if_pos (by omega), zero_add]

/-- The column of the check matrix at `(i, fixT i)`. -/
def blockVec (K ℓ r : ℕ) (i : Fin (K + 1)) : Fin (K + 1 - 1) ⊕ Fin ℓ → ZMod 2 :=
  fun row => checkMatrix (K + 1) ℓ row (i, fixT K ℓ r i)

/-- The unit vector of checksum row `t`. -/
noncomputable def unitVec (K ℓ : ℕ) (t : Fin ℓ) : Fin (K + 1 - 1) ⊕ Fin ℓ → ZMod 2 :=
  Pi.single (Sum.inr t) 1

/-- The free rows `t ≥ r`. -/
def freeRows (ℓ r : ℕ) : Finset (Fin ℓ) := Finset.univ.filter fun t => r ≤ (t : ℕ)

open Classical in
/-- The spanning set of `K + 1` block vectors and `ℓ - r` unit vectors. -/
noncomputable def spanSet (K ℓ r : ℕ) : Finset (Fin (K + 1 - 1) ⊕ Fin ℓ → ZMod 2) :=
  Finset.univ.image (blockVec K ℓ r) ∪ (freeRows ℓ r).image (unitVec K ℓ)

theorem card_spanSet (r : ℕ) : (spanSet K ℓ r).card ≤ K + 1 + (ℓ - r) := by
  classical
  unfold spanSet
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
  · exact Finset.card_image_le.trans (by simp)
  · exact Finset.card_image_le.trans (card_filter_ge r)

theorem col_mem_span (r : ℕ) (x : Coord (K + 1) ℓ)
    (hb : ∀ t : Fin ℓ, (t : ℕ) < r → x.2 t = fixBit K x.1) :
    (fun row => checkMatrix (K + 1) ℓ row x) ∈
      Submodule.span (ZMod 2) (spanSet K ℓ r : Set (Fin (K + 1 - 1) ⊕ Fin ℓ → ZMod 2)) := by
  classical
  rw [col_decomp r x hb]
  refine Submodule.add_mem _ (Submodule.subset_span ?_) (Submodule.sum_mem _ fun t ht => ?_)
  · show blockVec K ℓ r x.1 ∈ (spanSet K ℓ r : Set _)
    unfold spanSet
    exact Finset.mem_coe.mpr (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_univ x.1)))
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    show unitVec K ℓ t ∈ (spanSet K ℓ r : Set _)
    unfold spanSet
    exact Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ht))

/-- **Rank bound.** If all coordinates of the domain have fixed bits in the rows `t < r`, then
`rank B_e ≤ K + 1 + (ℓ - r)`. -/
theorem rank_le_of_fixedRows {r : ℕ} (D : Finset (Coord (K + 1) ℓ)) (hD : FixedRows r D) :
    (Matrix.of fun row (c : D) => checkMatrix (K + 1) ℓ row c).rank ≤ K + 1 + (ℓ - r) := by
  have hspan : Submodule.span (ZMod 2)
      (Set.range (Matrix.of fun row (c : D) => checkMatrix (K + 1) ℓ row c).col) ≤
        Submodule.span (ZMod 2) (spanSet K ℓ r : Set _) := by
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    have hc : (Matrix.of fun row (c : D) => checkMatrix (K + 1) ℓ row c).col c =
        fun row => checkMatrix (K + 1) ℓ row c.1 := rfl
    rw [hc]
    exact col_mem_span r c.1 (fun t ht => hD _ c.2 t ht)
  rw [Matrix.rank_eq_finrank_span_cols]
  exact (Submodule.finrank_mono hspan).trans
    ((finrank_span_finset_le_card (spanSet K ℓ r)).trans (card_spanSet r))

/-! ### Summation -/

theorem sum_pow_sub (ℓ : ℕ) : ∑ t ∈ Finset.range ℓ, 2 ^ (ℓ - t) + 2 = 2 ^ (ℓ + 1) := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    rw [Finset.sum_range_succ']
    have : ∀ t ∈ Finset.range ℓ, 2 ^ (ℓ + 1 - (t + 1)) = 2 ^ (ℓ - t) := fun t _ => by
      congr 1; omega
    rw [Finset.sum_congr rfl this, Nat.sub_zero, pow_succ 2 (ℓ + 1)]
    omega

theorem sum_pow_rows (hK : 0 < K) :
    ∑ j : Fin (ℓ * K), 2 ^ (ℓ - (j : ℕ) / K) ≤ K * 2 ^ (ℓ + 1) := by
  rw [← (pos K ℓ).sum_comp]
  have h1 : ∀ x : Fin ℓ × Fin K, ((pos K ℓ x : ℕ) / K) = x.1 := by
    intro x
    rw [pos_val, Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt x.2.2, zero_add]
  simp only [h1]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← Finset.mul_sum]
  gcongr
  rw [Fin.sum_univ_eq_sum_range (fun t => 2 ^ (ℓ - t)) ℓ]
  have := sum_pow_sub ℓ
  omega

theorem sum_domN (M : ℕ) (f : ℕ → ℕ) :
    ∑ n ∈ Finset.range (3 + 2 * M), f n =
      f 0 + f 1 + f 2 + ∑ j ∈ Finset.range M, (f (3 + 2 * j) + f (4 + 2 * j)) := by
  induction M with
  | zero => simp [Finset.sum_range_succ]
  | succ M ih =>
    rw [show 3 + 2 * (M + 1) = 3 + 2 * M + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring_nf

theorem card_supp_le (a : Arr K ℓ) : (supp a).card ≤ K + 1 :=
  Finset.card_image_le.trans (by simp)

theorem rowRank_le_of_fixedRows {w r : ℕ} (e : Schema (K + 1) ℓ w) (hD : FixedRows r e.domain) :
    rowRank e ≤ K + 1 + (ℓ - r) :=
  rank_le_of_fixedRows e.domain hD

/-- The contribution of a single schema. -/
theorem schema_bound (x : SchIdx K ℓ) :
    (schemaOf x).domain.card + 2 ^ rowRank (schemaOf x) ≤
      match x with
      | .inl _ => (K + 1) + 2 ^ (K + 1) * 2 ^ ℓ
      | .inr (j, _) => (K + 1 + 2 ^ (K + 1)) * 2 ^ (ℓ - (j : ℕ) / K) := by
  rcases x with b | ⟨j, c⟩
  · have hdom : ∃ a : Arr K ℓ, (schemaOf (.inl b)).domain = supp a := by
      cases b
      · exact ⟨0, rfl⟩
      · exact ⟨top K ℓ, rfl⟩
    obtain ⟨a, ha⟩ := hdom
    have h1 := rowRank_le_of_fixedRows (schemaOf (K := K) (ℓ := ℓ) (.inl b)) (fixedRows_zero _)
    have h2 : 2 ^ rowRank (schemaOf (K := K) (ℓ := ℓ) (.inl b)) ≤ 2 ^ (K + 1) * 2 ^ ℓ := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [ha]
    have := card_supp_le a
    dsimp only
    omega
  · have hdom : (schemaOf (.inr (j, c))).domain = dom K ℓ j := by
      fin_cases c <;> rfl
    have hfix : FixedRows ((j : ℕ) / K) (schemaOf (K := K) (ℓ := ℓ) (.inr (j, c))).domain := by
      rw [hdom]; exact fixedRows_dom j
    have h1 := rowRank_le_of_fixedRows _ hfix
    have h2 : 2 ^ rowRank (schemaOf (K := K) (ℓ := ℓ) (.inr (j, c))) ≤
        2 ^ (K + 1) * 2 ^ (ℓ - (j : ℕ) / K) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) h1
    have h3 := card_le_of_fixedRows hfix
    dsimp only
    rw [add_mul]
    omega

/-- **Size of the counter.** `rowSpaceSize(𝓘_ctr) ≤ C_K 2^ℓ`. -/
theorem sizeParameter_le (hK : 0 < K) : ∃ C : ℕ, ∀ ℓ : ℕ,
    rowSpaceSize (counter K ℓ) ≤ C * 2 ^ ℓ := by
  refine ⟨(K + 1) + 2 * (K + 1) + 2 * (K + 1) * (2 * K) +
    (K + 2) * (2 * (K + 1) + 2 * 2 ^ (K + 1) + 3 * (K + 1 + 2 ^ (K + 1)) * (2 * K)), fun ℓ => ?_⟩
  set A := 2 ^ ℓ with hA
  have hA1 : 1 ≤ A := Nat.one_le_two_pow
  set G := ∑ j : Fin (ℓ * K), 2 ^ (ℓ - (j : ℕ) / K) with hG
  have hGle : G ≤ 2 * K * A := by
    have := sum_pow_rows (ℓ := ℓ) hK
    rw [pow_succ] at this
    calc G ≤ K * (A * 2) := this
      _ = 2 * K * A := by ring
  -- the locations
  have hv : ∑ v : Fin (numLoc K ℓ), (domN K ℓ v).card ≤ (K + 1) * A + 2 * (K + 1) + 2 * (K + 1) * G := by
    rw [Fin.sum_univ_eq_sum_range (fun n => (domN K ℓ n).card), sum_domN]
    simp only [domN_p, domN_q]
    have h0 : (domN K ℓ 0).card = (K + 1) * A := by
      simp [domN, Finset.card_univ, ZMod.card, hA]
    have h1 : (domN K ℓ 1).card ≤ K + 1 := by simp only [domN]; simpa using card_supp_le _
    have h2 : (domN K ℓ 2).card ≤ K + 1 := by simp only [domN]; simpa using card_supp_le _
    have h3 : ∑ j ∈ Finset.range (ℓ * K), ((dom K ℓ j).card + (dom K ℓ j).card) ≤ 2 * (K + 1) * G := by
      rw [hG, ← Fin.sum_univ_eq_sum_range (fun j => (dom K ℓ j).card + (dom K ℓ j).card),
        Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => by
        have := card_le_of_fixedRows (fixedRows_dom (K := K) (ℓ := ℓ) j)
        nlinarith
    omega
  -- the schemas
  have hs : ((counter K ℓ).schemas.map fun e => e.domain.card + 2 ^ rowRank e).sum ≤
      2 * ((K + 1) + 2 ^ (K + 1) * A) + 3 * ((K + 1 + 2 ^ (K + 1)) * G) := by
    show (((Finset.univ : Finset (SchIdx K ℓ)).toList.map schemaOf).map
      fun e => e.domain.card + 2 ^ rowRank e).sum ≤ _
    rw [List.map_map, Finset.sum_map_toList]
    refine (Finset.sum_le_sum fun x _ => schema_bound x).trans (le_of_eq ?_)
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp [Finset.sum_const, Finset.card_univ, hG, Finset.mul_sum]
    ring
  have hP : 1 ≤ 2 ^ (K + 1) := Nat.one_le_two_pow
  have hv' : ∑ v : Fin (numLoc K ℓ), (domN K ℓ v).card ≤
      ((K + 1) + 2 * (K + 1) + 2 * (K + 1) * (2 * K)) * A := by
    calc _ ≤ (K + 1) * A + 2 * (K + 1) + 2 * (K + 1) * G := hv
      _ ≤ (K + 1) * A + 2 * (K + 1) * A + 2 * (K + 1) * (2 * K * A) :=
          Nat.add_le_add (Nat.add_le_add le_rfl (Nat.le_mul_of_pos_right _ hA1))
            (Nat.mul_le_mul_left _ hGle)
      _ = _ := by ring
  have hs' : ((counter K ℓ).schemas.map fun e => e.domain.card + 2 ^ rowRank e).sum ≤
      (2 * (K + 1) + 2 * 2 ^ (K + 1) + 3 * (K + 1 + 2 ^ (K + 1)) * (2 * K)) * A := by
    calc _ ≤ 2 * ((K + 1) + 2 ^ (K + 1) * A) + 3 * ((K + 1 + 2 ^ (K + 1)) * G) := hs
      _ ≤ 2 * ((K + 1) * A + 2 ^ (K + 1) * A) + 3 * ((K + 1 + 2 ^ (K + 1)) * (2 * K * A)) :=
          Nat.add_le_add
            (Nat.mul_le_mul_left 2 (Nat.add_le_add_right (Nat.le_mul_of_pos_right _ hA1) _))
            (Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left _ hGle))
      _ = _ := by ring
  calc rowSpaceSize (counter K ℓ)
      = ∑ v : Fin (numLoc K ℓ), (domN K ℓ v).card + (K + 1 + 1) *
          ((counter K ℓ).schemas.map fun e => e.domain.card + 2 ^ rowRank e).sum := rfl
    _ ≤ ((K + 1) + 2 * (K + 1) + 2 * (K + 1) * (2 * K)) * A + (K + 1 + 1) *
          ((2 * (K + 1) + 2 * 2 ^ (K + 1) + 3 * (K + 1 + 2 ^ (K + 1)) * (2 * K)) * A) :=
        Nat.add_le_add hv' (Nat.mul_le_mul_left _ hs')
    _ = _ := by ring

end Lax119563Proofs.Counter

end Counter_Size

/-! ### Formerly `Lax119563Proofs.Game.Colors` -/

section Game_Colors

/-!
# Basic facts about Weisfeiler–Leman colors

* the round-`r` color of a tuple determines its atomic type;
* the round-`r` color of a reindexed tuple `x ∘ g` is a function of the color of `x`;
* equal multisets over the vertex sets yield a color-preserving bijection.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman

namespace Lax119563Proofs.Game

/-- Two maps on finite types with equal value multisets are related by a bijection. -/
theorem exists_equiv_of_map_univ_eq {α β γ : Type*} [Fintype α] [Fintype β]
    (F : α → γ) (F' : β → γ)
    (h : (Finset.univ : Finset α).val.map F = (Finset.univ : Finset β).val.map F') :
    ∃ e : α ≃ β, ∀ a, F' (e a) = F a := by
  classical
  have hfib : ∀ c, Nonempty ({a // F a = c} ≃ {b // F' b = c}) := by
    intro c
    refine ⟨Fintype.equivOfCardEq ?_⟩
    have hc := congrArg (Multiset.count c) h
    simp only [Multiset.count_map] at hc
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa [Finset.card, Finset.filter_val, eq_comm] using hc
  exact ⟨Equiv.ofFiberEquiv (fun c => (hfib c).some), fun a => Equiv.ofFiberEquiv_map _ a⟩

variable {k : ℕ}

/-- The color in round `r + 1` determines the color in round `r`. -/
theorem color_eq_of_color_succ_eq {G H : ColoredGraph} {r : ℕ} {x : Fin k → Fin G.n}
    {y : Fin k → Fin H.n} (h : color G (r + 1) x = color H (r + 1) y) :
    color G r x = color H r y :=
  congrArg Prod.fst h

/-- Equal colors in round `r + 1` give equal multisets of substituted color tuples. -/
theorem multiset_eq_of_color_succ_eq {G H : ColoredGraph} {r : ℕ} {x : Fin k → Fin G.n}
    {y : Fin k → Fin H.n} (h : color G (r + 1) x = color H (r + 1) y) :
    (Finset.univ : Finset (Fin G.n)).val.map
        (fun q i => color G r (Function.update x i q)) =
      (Finset.univ : Finset (Fin H.n)).val.map
        (fun q i => color H r (Function.update y i q)) :=
  congrArg Prod.snd h

/-- The color in any round determines the atomic type. -/
theorem atp_eq_of_color_eq {G H : ColoredGraph} :
    ∀ {r : ℕ} {x : Fin k → Fin G.n} {y : Fin k → Fin H.n},
      color G r x = color H r y → atp G x = atp H y
  | 0, _, _, h => h
  | _ + 1, _, _, h => atp_eq_of_color_eq (color_eq_of_color_succ_eq h)

/-- Unpacking equality of atomic types. -/
theorem atp_eq_iff {G H : ColoredGraph} {x : Fin k → Fin G.n} {y : Fin k → Fin H.n} :
    atp G x = atp H y ↔ ∀ u v : Fin k, (x u = x v ↔ y u = y v) ∧
      (G.graph.Adj (x u) (x v) ↔ H.graph.Adj (y u) (y v)) ∧ G.color (x u) = H.color (y u) := by
  constructor
  · intro h u v
    have h1 := congrFun (congrFun (congrArg AtomicType.eq h) u) v
    have h2 := congrFun (congrFun (congrArg AtomicType.adj h) u) v
    have h3 := congrFun (congrArg AtomicType.color h) u
    simp only [atp, decide_eq_decide] at h1 h2 h3
    exact ⟨h1, h2, h3⟩
  · intro h
    simp only [atp, AtomicType.mk.injEq]
    refine ⟨funext fun u => funext fun v => ?_, funext fun u => funext fun v => ?_,
      funext fun u => (h u u).2.2⟩
    · exact decide_eq_decide.mpr (h u v).1
    · exact decide_eq_decide.mpr (h u v).2.1

/-- Substituting into a reindexed tuple is reindexing a substituted tuple. -/
theorem exists_update_comp (g : Fin k → Fin k) (j : Fin k) :
    ∃ l : Fin k, ∃ g' : Fin k → Fin k, ∀ {V : Type} (x : Fin k → V) (q : V),
      Function.update (x ∘ g) j q = Function.update x l q ∘ g' := by
  classical
  by_cases hl : ∃ l, ∀ m, g m ≠ l
  · obtain ⟨l, hl⟩ := hl
    refine ⟨l, Function.update g j l, fun x q => funext fun m => ?_⟩
    by_cases hm : m = j
    · subst hm; simp
    · simp [Function.update_of_ne hm, Function.update_of_ne (hl m)]
  · push Not at hl
    have hinj : Function.Injective g := Finite.injective_iff_surjective.mpr hl
    refine ⟨g j, g, fun x q => funext fun m => ?_⟩
    by_cases hm : m = j
    · subst hm; simp
    · simp [Function.update_of_ne hm, Function.update_of_ne (hinj.ne hm)]

/-- The color of a reindexed tuple `x ∘ g` is a function of the color of `x`. -/
theorem exists_color_comp :
    ∀ (r : ℕ) (g : Fin k → Fin k), ∃ F : Color k r → Color k r,
      ∀ (G : ColoredGraph) (x : Fin k → Fin G.n), color G r (x ∘ g) = F (color G r x)
  | 0, g => ⟨fun t => ⟨fun i j => t.eq (g i) (g j), fun i j => t.adj (g i) (g j),
      fun i => t.color (g i)⟩, fun G x => by simp only [color, atp]; congr⟩
  | r + 1, g => by
    obtain ⟨F0, hF0⟩ := exists_color_comp r g
    choose l g' hg using exists_update_comp g
    choose F hF using fun j => exists_color_comp r (g' j)
    refine ⟨fun c => (F0 c.1, c.2.map fun t j => F j (t (l j))), fun G x => ?_⟩
    refine Prod.ext (hF0 G x) ?_
    rw [color, color]
    dsimp only
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun q _ => funext fun j => ?_
    simp only [Function.comp_apply, hg, hF]

/-- Reindexing preserves equality of colors. -/
theorem color_comp_eq {G H : ColoredGraph} {r : ℕ} (g : Fin k → Fin k)
    {x : Fin k → Fin G.n} {y : Fin k → Fin H.n} (h : color G r x = color H r y) :
    color G r (x ∘ g) = color H r (y ∘ g) := by
  obtain ⟨F, hF⟩ := exists_color_comp r g
  rw [hF, hF, h]

end Lax119563Proofs.Game

end Game_Colors

/-! ### Formerly `Lax119563Proofs.Game.Duplicator` -/

section Game_Duplicator

/-!
# Duplicator's strategy from equal Weisfeiler–Leman colors

If `k`-WL does not distinguish `G` and `H` after `r` rounds, then Duplicator survives `r`
rounds of `BP_{k+1}(G, H)` from the empty game state.

Duplicator maintains the following invariant with `s` rounds remaining: for every pebble
index `i` that Spoiler may lift, the remaining `k` pebble indices `i.succAbove m` can be
read as slots of a pair of `k`-tuples `a`, `b` with equal round-`s` colors, where every
placed pebble pair `i.succAbove m` sits on `(a m, b m)` (unplaced pebbles impose nothing).
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.PebbleGame

namespace Lax119563Proofs.Game

variable {k : ℕ} {G H : ColoredGraph}

/-- Duplicator's invariant with `s` rounds remaining. -/
def DupInv (k s : ℕ) (G H : ColoredGraph) (S : GameState (k + 1) G H) : Prop :=
  ∀ i : Fin (k + 1), ∃ a : Fin k → Fin G.n, ∃ b : Fin k → Fin H.n,
    color G s a = color H s b ∧ ∀ m pq, S (i.succAbove m) = some pq → pq = (a m, b m)

/-- Two tuples with equal atomic types give a partial-isomorphism condition on any two
of their slots. -/
theorem pi_cond_of_atp_eq {x : Fin k → Fin G.n} {y : Fin k → Fin H.n}
    (h : atp G x = atp H y) (u v : Fin k) :
    (x u = x v ↔ y u = y v) ∧ (G.graph.Adj (x u) (x v) ↔ H.graph.Adj (y u) (y v)) ∧
      G.color (x u) = H.color (y u) :=
  atp_eq_iff.mp h u v

/-- Duplicator survives `s` rounds from any state satisfying the invariant. -/
theorem survivesFrom_of_dupInv (hk : 2 ≤ k) :
    ∀ (s : ℕ) (S : GameState (k + 1) G H), DupInv k s G H S → SurvivesFrom G H s S
  | 0, _, _ => trivial
  | s + 1, S, hS => by
    classical
    intro i
    obtain ⟨a, b, hab, hcomp⟩ := hS i
    have hab0 : color G s a = color H s b := color_eq_of_color_succ_eq hab
    obtain ⟨f, hf⟩ := exists_equiv_of_map_univ_eq _ _ (multiset_eq_of_color_succ_eq hab)
    have hf' : ∀ q l, color G s (Function.update a l q) =
        color H s (Function.update b l (f q)) := fun q l => (congrFun (hf q) l).symm
    refine ⟨f, fun q => ⟨?_, survivesFrom_of_dupInv hk s _ ?_⟩⟩
    · -- the new state is a partial isomorphism
      -- every placed pair other than pebble `i` sits in the slots of `a`, `b`
      have hother : ∀ j p p', j ≠ i →
          Function.update S i (some (q, f q)) j = some (p, p') →
            ∃ m, p = a m ∧ p' = b m := by
        intro j p p' hj h
        obtain ⟨m, rfl⟩ := Fin.exists_succAbove_eq hj
        rw [Function.update_of_ne hj] at h
        have := hcomp m _ h
        simp only [Prod.mk.injEq] at this
        exact ⟨m, this.1, this.2⟩
      have hself : ∀ p p', Function.update S i (some (q, f q)) i = some (p, p') →
          p = q ∧ p' = f q := by
        intro p p' h
        simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨h.1.symm, h.2.symm⟩
      have hatp : ∀ l, atp G (Function.update a l q) = atp H (Function.update b l (f q)) :=
        fun l => atp_eq_of_color_eq (hf' q l)
      -- a slot different from a given one
      have hother_slot : ∀ m : Fin k, ∃ l, l ≠ m := by
        intro m
        by_cases hm : m.val = 0
        · exact ⟨⟨1, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
        · exact ⟨⟨0, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
      intro j1 j2 p1 q1 p2 q2 h1 h2
      by_cases hj1 : j1 = i <;> by_cases hj2 : j2 = i
      · subst hj1 hj2
        obtain ⟨rfl, rfl⟩ := hself _ _ h1
        obtain ⟨rfl, rfl⟩ := hself _ _ h2
        have := pi_cond_of_atp_eq (hatp ⟨0, by omega⟩) ⟨0, by omega⟩ ⟨0, by omega⟩
        simpa using this
      · subst hj1
        obtain ⟨rfl, rfl⟩ := hself _ _ h1
        obtain ⟨m2, rfl, rfl⟩ := hother _ _ _ hj2 h2
        obtain ⟨l, hl⟩ := hother_slot m2
        have := pi_cond_of_atp_eq (hatp l) l m2
        simpa [Function.update_of_ne hl.symm] using this
      · subst hj2
        obtain ⟨m1, rfl, rfl⟩ := hother _ _ _ hj1 h1
        obtain ⟨rfl, rfl⟩ := hself _ _ h2
        obtain ⟨l, hl⟩ := hother_slot m1
        have := pi_cond_of_atp_eq (hatp l) m1 l
        simpa [Function.update_of_ne hl.symm] using this
      · obtain ⟨m1, rfl, rfl⟩ := hother _ _ _ hj1 h1
        obtain ⟨m2, rfl, rfl⟩ := hother _ _ _ hj2 h2
        exact pi_cond_of_atp_eq (atp_eq_of_color_eq hab0) m1 m2
    · -- the invariant is preserved
      intro i'
      by_cases hi : i' = i
      · subst hi
        refine ⟨a, b, hab0, fun m pq h => ?_⟩
        rw [Function.update_of_ne (Fin.succAbove_ne _ _)] at h
        exact hcomp m pq h
      · obtain ⟨l0, hl0⟩ := Fin.exists_succAbove_eq hi
        let g : Fin k → Fin k := fun m =>
          if h : i'.succAbove m = i then l0
          else Classical.choose (Fin.exists_succAbove_eq h)
        refine ⟨Function.update a l0 q ∘ g, Function.update b l0 (f q) ∘ g,
          color_comp_eq g (hf' q l0), fun m pq h => ?_⟩
        by_cases hm : i'.succAbove m = i
        · rw [hm, Function.update_self] at h
          simp only [Option.some.injEq] at h
          subst h
          simp [g, hm]
        · have hspec := Classical.choose_spec (Fin.exists_succAbove_eq hm)
          set m' := Classical.choose (Fin.exists_succAbove_eq hm)
          have hgm : g m = m' := by simp [g, hm, m']
          have hm' : m' ≠ l0 := by
            rintro rfl
            rw [hl0] at hspec
            exact Fin.succAbove_ne i' m hspec.symm
          rw [Function.update_of_ne hm, ← hspec] at h
          simp only [Function.comp_apply, hgm, Function.update_of_ne hm']
          exact hcomp m' pq h

/-- Duplicator survives from any state if both graphs are empty. -/
theorem survivesFrom_of_n_eq_zero (hG : G.n = 0) (hH : H.n = 0) {m : ℕ} :
    ∀ (s : ℕ) (S : GameState m G H), SurvivesFrom G H s S
  | 0, _ => trivial
  | _ + 1, _ => fun _ => ⟨finCongr (hG.trans hH.symm), fun p => absurd p.isLt (by omega)⟩

/-- Equal color counts in round `r` give fiberwise bijections between the color classes. -/
theorem fiber_equivs_of_not_distinguishesAfter {r : ℕ} (h : ¬ DistinguishesAfter k r G H)
    (c : Color k r) :
    Nonempty ({p : Fin k → Fin G.n // color G r p = c} ≃
      {q : Fin k → Fin H.n // color H r q = c}) := by
  classical
  simp only [DistinguishesAfter, not_exists, not_not] at h
  exact ⟨Fintype.equivOfCardEq (by simpa [Nat.card_eq_fintype_card] using h c)⟩

/-- If `k`-WL does not distinguish `G` and `H` after `r` rounds, Duplicator survives `r`
rounds of `BP_{k+1}(G, H)`. -/
theorem duplicatorSurvives_of_not_distinguishesAfter (hk : 2 ≤ k) {r : ℕ}
    (h : ¬ DistinguishesAfter k r G H) : DuplicatorSurvives (k + 1) r G H := by
  have e := fun c => (fiber_equivs_of_not_distinguishesAfter h c).some
  have hn : G.n = H.n := by
    have := Fintype.card_congr (Equiv.ofFiberEquiv e)
    simp only [Fintype.card_fun, Fintype.card_fin] at this
    exact Nat.pow_left_injective (by omega) this
  refine ⟨hn, ?_⟩
  by_cases hG : G.n = 0
  · exact survivesFrom_of_n_eq_zero hG (hn ▸ hG) _ _
  · refine survivesFrom_of_dupInv hk r _ fun i => ?_
    let a : Fin k → Fin G.n := fun _ => ⟨0, by omega⟩
    let b := e (color G r a) ⟨a, rfl⟩
    exact ⟨a, b.1, b.2.symm, fun m pq h => by simp at h⟩

end Lax119563Proofs.Game

end Game_Duplicator

/-! ### Formerly `Lax119563Proofs.Game.Spoiler` -/

section Game_Spoiler

/-!
# Spoiler's strategy from a Weisfeiler–Leman distinction

If `k`-WL distinguishes `G` and `H` after `r` rounds, then Spoiler wins `BP_{k+1}(G, H)`
within `r + k` rounds: in the first `k` rounds he places pebbles `0, …, k-1` so that the
numbers of extensions with a fixed round-`r` color keep differing, ending in two
`k`-tuples with different round-`r` colors; from there `r` further rounds suffice.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.PebbleGame

namespace Lax119563Proofs.Game

variable {k : ℕ} {G H : ColoredGraph}

/-- Surviving `s + 1` rounds implies surviving `s` rounds. -/
theorem survivesFrom_of_succ {m : ℕ} :
    ∀ (s : ℕ) (S : GameState m G H), SurvivesFrom G H (s + 1) S → SurvivesFrom G H s S
  | 0, _, _ => trivial
  | s + 1, _, h => fun i =>
    let ⟨f, hf⟩ := h i
    ⟨f, fun p => ⟨(hf p).1, survivesFrom_of_succ s _ (hf p).2⟩⟩

/-- If pebbles `σ m` carry tuples `a`, `b` with different round-`s` colors, then the state
is not a partial isomorphism from which Duplicator survives `s` rounds. -/
theorem not_survivesFrom_of_color_ne :
    ∀ (s : ℕ) (S : GameState (k + 1) G H) (σ : Fin k → Fin (k + 1)), Function.Injective σ →
      ∀ (a : Fin k → Fin G.n) (b : Fin k → Fin H.n), (∀ m, S (σ m) = some (a m, b m)) →
        color G s a ≠ color H s b → ¬ (IsPartialIso G H S ∧ SurvivesFrom G H s S)
  | 0, S, σ, _, a, b, hS, hne, ⟨hPI, _⟩ =>
    hne (atp_eq_iff.mpr fun u v => hPI (σ u) (σ v) _ _ _ _ (hS u) (hS v))
  | s + 1, S, σ, hσ, a, b, hS, hne, ⟨hPI, hsurv⟩ => by
    classical
    by_cases h0 : color G s a = color H s b
    swap
    · exact not_survivesFrom_of_color_ne s S σ hσ a b hS h0
        ⟨hPI, survivesFrom_of_succ s S hsurv⟩
    have hmul : (Finset.univ : Finset (Fin G.n)).val.map
          (fun q l => color G s (Function.update a l q)) ≠
        (Finset.univ : Finset (Fin H.n)).val.map
          (fun q l => color H s (Function.update b l q)) := fun hm => hne (Prod.ext h0 hm)
    -- a pebble index not used by `σ`
    obtain ⟨i0, hi0⟩ : ∃ i0, ∀ m, σ m ≠ i0 := by
      by_contra hcon
      push Not at hcon
      have := Fintype.card_le_of_surjective σ fun i => (hcon i).imp fun _ h => h
      simp at this
    obtain ⟨f, hf⟩ := hsurv i0
    obtain ⟨q, hq⟩ : ∃ q, (fun l => color G s (Function.update a l q)) ≠
        (fun l => color H s (Function.update b l (f q))) := by
      by_contra hcon
      push Not at hcon
      apply hmul
      rw [show (fun q l => color G s (Function.update a l q)) =
          (fun q l => color H s (Function.update b l q)) ∘ f from funext hcon,
        ← Multiset.map_map, Multiset.map_univ_val_equiv]
    obtain ⟨l, hl⟩ := Function.ne_iff.mp hq
    refine not_survivesFrom_of_color_ne s (Function.update S i0 (some (q, f q)))
      (Function.update σ l i0) ?_ (Function.update a l q) (Function.update b l (f q)) ?_ hl
      (hf q)
    · intro u v huv
      by_cases hu : u = l <;> by_cases hv : v = l
      · rw [hu, hv]
      · subst hu
        simp only [Function.update_self, Function.update_of_ne hv] at huv
        exact absurd huv.symm (hi0 v)
      · subst hv
        simp only [Function.update_self, Function.update_of_ne hu] at huv
        exact absurd huv (hi0 u)
      · simp only [Function.update_of_ne hu, Function.update_of_ne hv] at huv
        exact hσ huv
    · intro m
      by_cases hm : m = l
      · subst hm; simp
      · simp only [Function.update_of_ne hm, Function.update_of_ne (hi0 m)]
        exact hS m

/-- The number of `k`-tuples of `G` that agree with `a` on the first `j` entries and have
round-`s` color `c`. -/
noncomputable def prefixCount (G : ColoredGraph) (s j : ℕ) (a : Fin k → Fin G.n)
    (c : Color k s) : ℕ := by
  classical
  exact (Finset.univ.filter fun p : Fin k → Fin G.n =>
    (∀ m : Fin k, m.val < j → p m = a m) ∧ color G s p = c).card

/-- Splitting the prefix count according to entry `j`. -/
theorem prefixCount_eq_sum (s j : ℕ) (a : Fin k → Fin G.n) (c : Color k s) (m0 : Fin k)
    (hm0 : m0.val = j) :
    prefixCount G s j a c = ∑ q, prefixCount G s (j + 1) (Function.update a m0 q) c := by
  classical
  unfold prefixCount
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p => p m0) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.filter_filter]
  congr 1
  refine Finset.filter_congr fun p _ => ?_
  constructor
  · rintro ⟨⟨hpre, hc⟩, hq⟩
    refine ⟨fun m hm => ?_, hc⟩
    by_cases hmm : m = m0
    · subst hmm; simpa using hq
    · rw [Function.update_of_ne hmm]
      exact hpre m (by have : m.val ≠ j := fun h => hmm (Fin.ext (h.trans hm0.symm)); omega)
  · rintro ⟨hpre, hc⟩
    refine ⟨⟨fun m hm => ?_, hc⟩, ?_⟩
    · have hmm : m ≠ m0 := fun h => by subst h; omega
      simpa [Function.update_of_ne hmm] using hpre m (by omega)
    · simpa using hpre m0 (by omega)

open Classical in
/-- The prefix count over all entries is the indicator of the color of the tuple. -/
theorem prefixCount_full (s : ℕ) (a : Fin k → Fin G.n) (c : Color k s) :
    prefixCount G s k a c = if color G s a = c then 1 else 0 := by
  classical
  unfold prefixCount
  have hfa : ∀ p : Fin k → Fin G.n, (∀ m : Fin k, m.val < k → p m = a m) ↔ p = a :=
    fun p => ⟨fun h => funext fun m => h m m.isLt, fun h m _ => h ▸ rfl⟩
  simp only [hfa]
  split_ifs with h
  · rw [Finset.card_eq_one]
    exact ⟨a, Finset.ext fun p => by simp only [Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton]; exact ⟨fun h' => h'.1, fun h' => ⟨h', h' ▸ h⟩⟩⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro p - ⟨rfl, h'⟩
    exact h h'

/-- If, after the first `j` pebbles are placed on prefixes of `a` and `b`, some round-`s`
color has different numbers of extensions, then Duplicator does not survive the remaining
`s + t` rounds, where `j + t = k`. -/
theorem not_survivesFrom_of_prefixCount_ne (s : ℕ) :
    ∀ (t j : ℕ), j + t = k → ∀ (S : GameState (k + 1) G H) (a : Fin k → Fin G.n)
      (b : Fin k → Fin H.n), (∀ m : Fin k, m.val < j → S m.castSucc = some (a m, b m)) →
      (∃ c, prefixCount G s j a c ≠ prefixCount H s j b c) →
      ¬ (IsPartialIso G H S ∧ SurvivesFrom G H (s + t) S)
  | 0, j, hj, S, a, b, hS, ⟨c, hc⟩ => by
    have hjk : j = k := by omega
    subst j
    refine not_survivesFrom_of_color_ne s S Fin.castSucc (Fin.castSucc_injective k) a b
      (fun m => hS m m.isLt) fun heq => hc ?_
    rw [prefixCount_full, prefixCount_full, heq]
  | t + 1, j, hj, S, a, b, hS, ⟨c, hc⟩ => by
    rintro ⟨_, hsurv⟩
    let m0 : Fin k := ⟨j, by omega⟩
    obtain ⟨f, hf⟩ := hsurv m0.castSucc
    obtain ⟨q, hq⟩ : ∃ q, prefixCount G s (j + 1) (Function.update a m0 q) c ≠
        prefixCount H s (j + 1) (Function.update b m0 (f q)) c := by
      by_contra hcon
      push Not at hcon
      apply hc
      rw [prefixCount_eq_sum s j a c m0 rfl, prefixCount_eq_sum s j b c m0 rfl,
        ← Equiv.sum_comp f]
      exact Finset.sum_congr rfl fun q _ => hcon q
    refine not_survivesFrom_of_prefixCount_ne s t (j + 1) (by omega) _
      (Function.update a m0 q) (Function.update b m0 (f q)) (fun m hm => ?_) ⟨c, hq⟩ (hf q)
    by_cases hmm : m = m0
    · subst hmm; simp
    · have hne : m.castSucc ≠ m0.castSucc := fun h => hmm (Fin.castSucc_injective k h)
      rw [Function.update_of_ne hne, Function.update_of_ne hmm, Function.update_of_ne hmm]
      exact hS m (by have : m.val ≠ j := fun h => hmm (Fin.ext h); omega)

/-- If `k`-WL distinguishes `G` and `H` after `r` rounds, Spoiler wins `BP_{k+1}(G, H)`
within `r + k` rounds. -/
theorem spoilerWinsWithin_of_distinguishesAfter' (hk : 1 ≤ k) {r : ℕ}
    (h : DistinguishesAfter k r G H) : SpoilerWinsWithin (k + 1) (r + k) G H := by
  classical
  rintro ⟨hn, hsurv⟩
  obtain ⟨c, hc⟩ := h
  by_cases hG : G.n = 0
  · have h0 : ∀ {n : ℕ}, n = 0 → ∀ P : (Fin k → Fin n) → Prop, Nat.card {p // P p} = 0 := by
      intro n hn0 P
      rw [Nat.card_eq_zero]
      left
      exact ⟨fun p => absurd (p.1 ⟨0, hk⟩).isLt (by omega)⟩
    exact hc ((h0 hG _).trans (h0 (hn ▸ hG) _).symm)
  refine not_survivesFrom_of_prefixCount_ne r k 0 (by omega) (fun _ => none)
    (fun _ => ⟨0, by omega⟩) (fun _ => ⟨0, by omega⟩) (fun m hm => absurd hm (by omega))
    ⟨c, ?_⟩ ⟨fun _ _ _ _ _ _ h => by simp at h, hsurv⟩
  simpa [prefixCount, Nat.card_eq_fintype_card, Fintype.card_subtype] using hc

end Lax119563Proofs.Game

end Game_Spoiler

/-! ### Formerly `Lax119563Proofs.HomTensors.BagTree` -/

section HomTensors_BagTree

/-!
# Rooted bag trees

A `BagTree V` is a finite rooted tree, given by parent pointers that strictly decrease a depth
function, with a bag of vertices of `V` at every node. Such trees are easy to combine (a new root
with several subtrees below it), and every bag tree satisfying the conditions of `BagTree.Valid`
yields a tree decomposition (in the sense of `Lax228581.Treewidth`) of every graph obtained by
identifying vertices along an "equality" relation whose pairs sit in equal or adjacent bags.
-/

namespace Lax119563Proofs.HomTensors

open Lax228581.Treewidth Relation

/-- A finite rooted tree with parent pointers decreasing a depth, with bags of vertices. -/
structure BagTree (V : Type) where
  /-- The nodes. -/
  I : Type
  [fin : Fintype I]
  /-- The root. -/
  root : I
  /-- The parent of a node (arbitrary at the root). -/
  parent : I → I
  /-- The depth, strictly decreasing towards the root. -/
  depth : I → ℕ
  depth_lt : ∀ t, t ≠ root → depth (parent t) < depth t
  /-- The bag at a node. -/
  bag : I → Finset V

attribute [instance] BagTree.fin

namespace BagTree

variable {V : Type} (T : BagTree V)

/-- `t` is the topmost node whose bag contains `a`: its bag contains `a` and either it is the
root or its parent's bag does not contain `a`. -/
def IsTop (a : V) (t : T.I) : Prop :=
  a ∈ T.bag t ∧ (t = T.root ∨ a ∉ T.bag (T.parent t))

lemma parent_ne {t : T.I} (ht : t ≠ T.root) : T.parent t ≠ t := fun h => by
  have := T.depth_lt t ht
  rw [h] at this
  exact lt_irrefl _ this

/-- The tree: every non-root node is adjacent to its parent. -/
def graph : SimpleGraph T.I where
  Adj s t := (s ≠ T.root ∧ T.parent s = t) ∨ (t ≠ T.root ∧ T.parent t = s)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun s h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact T.parent_ne h1 h2⟩

lemma graph_adj_parent {t : T.I} (ht : t ≠ T.root) : T.graph.Adj t (T.parent t) :=
  Or.inl ⟨ht, rfl⟩

lemma reachable_root (t : T.I) : T.graph.Reachable t T.root := by
  induction h : T.depth t using Nat.strong_induction_on generalizing t with
  | _ n ih =>
    by_cases ht : t = T.root
    · subst ht; rfl
    · exact (T.graph_adj_parent ht).reachable.trans (ih _ (h ▸ T.depth_lt t ht) _ rfl)

lemma connected : T.graph.Connected :=
  (SimpleGraph.connected_iff_exists_forall_reachable _).2
    ⟨T.root, fun w => (T.reachable_root w).symm⟩

lemma isTree : T.graph.IsTree := by
  classical
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨T.connected, ?_⟩
  let f : {t : T.I // t ≠ T.root} → T.graph.edgeSet := fun t =>
    ⟨s(t.1, T.parent t.1), T.graph_adj_parent t.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨t, ht⟩ ⟨t', ht'⟩ h
      have h := congrArg Subtype.val h
      simp only [f] at h
      rw [Sym2.eq_iff] at h
      rcases h with ⟨h, -⟩ | ⟨h1, h2⟩
      · exact Subtype.ext h
      · exfalso
        have a := T.depth_lt t ht
        have b := T.depth_lt t' ht'
        rw [h2] at a; rw [← h1] at b
        omega
    · rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | _ x y =>
        rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨⟨x, h1⟩, by simp [f, h2]⟩
        · exact ⟨⟨y, h1⟩, by simp [f, h2, Sym2.eq_swap]⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have := Fintype.card_subtype_compl (fun t : T.I => t = T.root)
  simp only [Fintype.card_unique] at this
  have hpos : 0 < Fintype.card T.I := Fintype.card_pos_iff.2 ⟨T.root⟩
  rw [this]
  omega

/-- Validity of a bag tree for a vertex set with an edge relation `adj` and an equality
relation `eqv`. -/
structure Valid (adj eqv : V → V → Prop) : Prop where
  cover : ∀ a, ∃ t, a ∈ T.bag t
  edge : ∀ a b, adj a b → ∃ t, a ∈ T.bag t ∧ b ∈ T.bag t
  eqv : ∀ a b, eqv a b → ∃ t s, a ∈ T.bag t ∧ b ∈ T.bag s ∧
    (s = t ∨ (t ≠ T.root ∧ s = T.parent t))
  top : ∀ a t s, T.IsTop a t → T.IsTop a s → t = s

section Reach

variable (S : Set T.I)

/-- Reachability inside the subtree induced by `S`, as a relation on nodes. -/
def Reach (t s : T.I) : Prop :=
  ∃ (ht : t ∈ S) (hs : s ∈ S), (T.graph.induce S).Reachable ⟨t, ht⟩ ⟨s, hs⟩

variable {T S}

lemma Reach.refl {t : T.I} (ht : t ∈ S) : T.Reach S t t := ⟨ht, ht, by rfl⟩

lemma Reach.symm {t s : T.I} (h : T.Reach S t s) : T.Reach S s t := by
  obtain ⟨ht, hs, h⟩ := h
  exact ⟨hs, ht, h.symm⟩

lemma Reach.trans {t s u : T.I} (h₁ : T.Reach S t s) (h₂ : T.Reach S s u) : T.Reach S t u := by
  obtain ⟨ht, hs, h₁⟩ := h₁
  obtain ⟨_, hu, h₂⟩ := h₂
  exact ⟨ht, hu, h₁.trans h₂⟩

lemma Reach.parent {t : T.I} (ht : t ≠ T.root) (h₁ : t ∈ S) (h₂ : T.parent t ∈ S) :
    T.Reach S t (T.parent t) :=
  ⟨h₁, h₂, SimpleGraph.Adj.reachable (G := T.graph.induce S) (T.graph_adj_parent ht)⟩

lemma reach_top {a : V} (hS : ∀ t, a ∈ T.bag t → t ∈ S) (t : T.I) (ha : a ∈ T.bag t) :
    ∃ s, T.IsTop a s ∧ T.Reach S t s := by
  induction h : T.depth t using Nat.strong_induction_on generalizing t with
  | _ n ih =>
    by_cases htop : t = T.root ∨ a ∉ T.bag (T.parent t)
    · exact ⟨t, ⟨ha, htop⟩, Reach.refl (hS t ha)⟩
    · push Not at htop
      obtain ⟨s, hs, hr⟩ := ih _ (h ▸ T.depth_lt t htop.1) _ htop.2 rfl
      exact ⟨s, hs, (Reach.parent htop.1 (hS t ha) (hS _ htop.2)).trans hr⟩

lemma reach_of_mem {adj eqv : V → V → Prop} (hT : T.Valid adj eqv) {a : V}
    (hS : ∀ t, a ∈ T.bag t → t ∈ S) {t s : T.I} (ht : a ∈ T.bag t) (hs : a ∈ T.bag s) :
    T.Reach S t s := by
  obtain ⟨t', ht', h1⟩ := reach_top hS t ht
  obtain ⟨s', hs', h2⟩ := reach_top hS s hs
  rw [hT.top a t' s' ht' hs'] at h1
  exact h1.trans h2.symm

end Reach

/-- A valid bag tree yields a tree decomposition of any graph `S` on a quotient `W` of `V`
whose kernel is generated by `eqv` and whose edges come from `adj`. -/
theorem hasTreewidthAtMost {adj eqv : V → V → Prop} (hT : T.Valid adj eqv)
    {W : Type} (S : SimpleGraph W) (π : V → W) (hπ : Function.Surjective π)
    (hker : ∀ a b, π a = π b → EqvGen eqv a b) (hcompat : ∀ a b, eqv a b → π a = π b)
    (hS : ∀ x y, S.Adj x y → ∃ a b, π a = x ∧ π b = y ∧ (adj a b ∨ adj b a))
    (w : ℕ) (hw : ∀ t, (T.bag t).card ≤ w + 1) : HasTreewidthAtMost S w := by
  classical
  have hcompat' : ∀ a b, EqvGen eqv a b → π a = π b := by
    intro a b h
    induction h with
    | rel x y h => exact hcompat x y h
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  refine ⟨{
      Node := T.I
      tree := T.graph
      isTree := T.isTree
      bag := fun t => (T.bag t).image π
      vertex_mem_bag := ?_
      edge_mem_bag := ?_
      bag_indices_connected := ?_ }, ?_⟩
  · intro x
    obtain ⟨a, rfl⟩ := hπ x
    obtain ⟨t, ht⟩ := hT.cover a
    exact ⟨t, Finset.mem_image_of_mem _ ht⟩
  · intro x y hxy
    obtain ⟨a, b, rfl, rfl, hab⟩ := hS x y hxy
    rcases hab with hab | hab
    · obtain ⟨t, ha, hb⟩ := hT.edge a b hab
      exact ⟨t, Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ hb⟩
    · obtain ⟨t, hb, ha⟩ := hT.edge b a hab
      exact ⟨t, Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ hb⟩
  · intro x
    set S' : Set T.I := {i | x ∈ (T.bag i).image π}
    obtain ⟨a₀, rfl⟩ := hπ x
    obtain ⟨t₀, ht₀⟩ := hT.cover a₀
    have memS : ∀ {a t}, π a = π a₀ → a ∈ T.bag t → t ∈ S' := fun ha ht =>
      Finset.mem_image.2 ⟨_, ht, ha⟩
    -- all bags of `π`-equivalent vertices are mutually reachable inside `S'`
    have key : ∀ a b, EqvGen eqv a b → π a = π a₀ →
        ∀ t s, a ∈ T.bag t → b ∈ T.bag s → T.Reach S' t s := by
      intro a b h
      induction h with
      | rel a b hab =>
        intro ha t s hat hbs
        have hb : π b = π a₀ := (hcompat a b hab).symm.trans ha
        obtain ⟨t', s', hat', hbs', h⟩ := hT.eqv a b hab
        have r1 := reach_of_mem hT (fun u hu => memS ha hu) hat hat'
        have r3 := reach_of_mem hT (fun u hu => memS hb hu) hbs' hbs
        have r2 : T.Reach S' t' s' := by
          rcases h with rfl | ⟨hne, rfl⟩
          · exact Reach.refl (memS ha hat')
          · exact Reach.parent hne (memS ha hat') (memS hb hbs')
        exact r1.trans (r2.trans r3)
      | refl a =>
        intro ha t s hat has
        exact reach_of_mem hT (fun u hu => memS ha hu) hat has
      | symm a b hab ih =>
        intro hb t s hbt has
        have ha : π a = π a₀ := (hcompat' a b hab).trans hb
        exact (ih ha s t has hbt).symm
      | trans a b c hab hbc ih1 ih2 =>
        intro ha t s hat hcs
        have hb : π b = π a₀ := (hcompat' a b hab).symm.trans ha
        obtain ⟨u, hu⟩ := hT.cover b
        exact (ih1 ha t u hat hu).trans (ih2 hb u s hu hcs)
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨t₀, memS rfl ht₀⟩, ?_⟩
    rintro ⟨s, hs⟩
    obtain ⟨b, hbs, hb⟩ := Finset.mem_image.1 hs
    obtain ⟨_, _, h⟩ := key a₀ b (hker _ _ hb.symm) rfl t₀ s ht₀ hbs
    exact h
  · intro t
    exact (Finset.card_image_le).trans (hw t)

end BagTree

end Lax119563Proofs.HomTensors

end HomTensors_BagTree

/-! ### Formerly `Lax119563Proofs.HomTensors.LGraph` -/

section HomTensors_LGraph

/-!
# Labeled graphs and their homomorphism tensors

A `k`-labeled graph `LGraph k` has a finite vertex type, an arbitrary edge relation (loops and
both orientations allowed; repeated edges are irrelevant for homomorphism counts), unary color
predicates, an *equality relation* `eqv`, and `k` labels. A homomorphism into a colored graph
must map edges to edges, respect the color predicates, and identify `eqv`-related vertices.
The equality relation replaces the identification of vertices by quotients during gluing; the
quotient is taken once, at the very end.

Goodness `Good F N` records a valid rooted bag tree of width `k` whose root bag contains all
labels, and that up to `eqv` the graph has at most `N` vertices besides the labels.

The basic construction is `glue`: a fresh set `L` of vertices together with a family of labeled
graphs, the labels of the `j`-th of which are identified with `σ j : Fin k → L`.
-/

namespace Lax119563Proofs.HomTensors

open Lax119563.ColoredGraphs Relation

/-- A `k`-labeled graph with edge relation, color predicates and equality constraints. -/
structure LGraph (k : ℕ) where
  /-- The vertices. -/
  V : Type
  [fin : Fintype V]
  /-- The edge relation. -/
  adj : V → V → Prop
  /-- Color predicates: `pred a c` requires vertex `a` to have color `c`. -/
  pred : V → ℕ → Prop
  /-- Equality constraints. -/
  eqv : V → V → Prop
  /-- The labels. -/
  lab : Fin k → V

attribute [instance] LGraph.fin

namespace LGraph

variable {k : ℕ}

/-- `h` is a homomorphism from `F` to the colored graph `G`. -/
def IsHom (F : LGraph k) (G : ColoredGraph) (h : F.V → Fin G.n) : Prop :=
  (∀ a b, F.adj a b → G.graph.Adj (h a) (h b)) ∧ (∀ a c, F.pred a c → G.color (h a) = c) ∧
    (∀ a b, F.eqv a b → h a = h b)

/-- The homomorphism tensor: the number of homomorphisms mapping the labels to `v`. -/
noncomputable def tensor (F : LGraph k) (G : ColoredGraph) (v : Fin k → Fin G.n) : ℕ :=
  Nat.card {h : F.V → Fin G.n // F.IsHom G h ∧ h ∘ F.lab = v}

/-- The number of homomorphisms. -/
noncomputable def homCount (F : LGraph k) (G : ColoredGraph) : ℕ :=
  Nat.card {h : F.V → Fin G.n // F.IsHom G h}

lemma sum_tensor (F : LGraph k) (G : ColoredGraph) : ∑ v, F.tensor G v = F.homCount G := by
  classical
  unfold tensor homCount
  rw [← Nat.card_sigma]
  refine Nat.card_congr ?_
  exact
    { toFun := fun p => ⟨p.2.1, p.2.2.1⟩
      invFun := fun h => ⟨h.1 ∘ F.lab, h.1, h.2, rfl⟩
      left_inv := by
        rintro ⟨v, h, hh, rfl⟩
        rfl
      right_inv := fun h => rfl }

/-- Bag-tree data for a labeled graph. -/
structure Decomp (F : LGraph k) where
  /-- The bag tree. -/
  T : BagTree F.V
  valid : T.Valid F.adj F.eqv
  width : ∀ t, (T.bag t).card ≤ k + 1
  root_lab : ∀ i, F.lab i ∈ T.bag T.root

/-- Up to `eqv`, `F` has at most `N` vertices besides its labels. -/
def Small (F : LGraph k) (N : ℕ) : Prop :=
  ∃ (W : Type) (g : W → F.V), Finite W ∧ Nat.card W ≤ N ∧
    ∀ a, (∃ i, EqvGen F.eqv a (F.lab i)) ∨ ∃ w, EqvGen F.eqv a (g w)

/-- Good labeled graphs: a bag tree of width `k` with all labels in the root bag, and at most
`N` vertices besides the labels. -/
def Good (F : LGraph k) (N : ℕ) : Prop :=
  Nonempty F.Decomp ∧ F.Small N

lemma Small.mono {F : LGraph k} {N N' : ℕ} (h : F.Small N) (hN : N ≤ N') : F.Small N' := by
  obtain ⟨W, g, hW, hc, hg⟩ := h
  exact ⟨W, g, hW, hc.trans hN, hg⟩

lemma Good.mono {F : LGraph k} {N N' : ℕ} (h : F.Good N) (hN : N ≤ N') : F.Good N' :=
  ⟨h.1, h.2.mono hN⟩

/-! ### Atoms -/

/-- A labeled graph whose vertices are exactly its `k` (distinct) labels. -/
def atom (adj : Fin k → Fin k → Prop) (pred : Fin k → ℕ → Prop) (eqv : Fin k → Fin k → Prop) :
    LGraph k where
  V := Fin k
  adj := adj
  pred := pred
  eqv := eqv
  lab := id

open scoped Classical in
lemma tensor_atom (adj : Fin k → Fin k → Prop) (pred : Fin k → ℕ → Prop)
    (eqv : Fin k → Fin k → Prop) (G : ColoredGraph) (v : Fin k → Fin G.n) :
    (atom adj pred eqv).tensor G v = if (atom adj pred eqv).IsHom G v then 1 else 0 := by
  classical
  unfold tensor
  split_ifs with h
  · rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨v, h, rfl⟩, ?_⟩
    rintro ⟨w, hw, rfl⟩
    rfl
  · rw [Nat.card_eq_zero]
    left
    refine ⟨fun ⟨w, hw, hwv⟩ => h ?_⟩
    subst hwv
    exact hw

lemma good_atom (adj : Fin k → Fin k → Prop) (pred : Fin k → ℕ → Prop)
    (eqv : Fin k → Fin k → Prop) : (atom adj pred eqv).Good 0 := by
  classical
  let T : BagTree (atom adj pred eqv).V :=
    { I := Unit
      root := ()
      parent := id
      depth := fun _ => 0
      depth_lt := fun t ht => absurd rfl ht
      bag := fun _ => Finset.univ }
  refine ⟨⟨{
      T := T
      valid := ?_
      width := ?_
      root_lab := ?_ }⟩, ?_⟩
  · refine ⟨fun a => ⟨(), Finset.mem_univ _⟩, fun a b _ => ⟨(), Finset.mem_univ _,
      Finset.mem_univ _⟩, fun a b _ => ⟨(), (), Finset.mem_univ _, Finset.mem_univ _,
      Or.inl rfl⟩, fun a t s _ _ => rfl⟩
  · intro t
    show (Finset.univ : Finset (Fin k)).card ≤ k + 1
    simp
  · intro i
    exact Finset.mem_univ _
  · exact ⟨Empty, Empty.elim, inferInstance, by simp, fun a => Or.inl ⟨a, EqvGen.refl _⟩⟩

/-! ### Gluing -/

section Glue

variable (L : Type) [Fintype L] (lam : Fin k → L) (J : Type) [Fintype J] (F : J → LGraph k)
  (σ : J → Fin k → L)

/-- Glue the graphs `F j` onto a fresh vertex set `L`, identifying the `i`-th label of `F j`
with `σ j i`; the new labels are `lam`. -/
def glue : LGraph k where
  V := L ⊕ Σ j, (F j).V
  adj a b := ∃ j x y, (F j).adj x y ∧ a = .inr ⟨j, x⟩ ∧ b = .inr ⟨j, y⟩
  pred a c := ∃ j x, (F j).pred x c ∧ a = .inr ⟨j, x⟩
  eqv a b := (∃ j x y, (F j).eqv x y ∧ a = .inr ⟨j, x⟩ ∧ b = .inr ⟨j, y⟩) ∨
    ∃ j i, a = .inr ⟨j, (F j).lab i⟩ ∧ b = .inl (σ j i)
  lab i := .inl (lam i)

/-- Homomorphisms from a glued graph split into a map on `L` and homomorphisms of the parts. -/
def glueHomEquiv (G : ColoredGraph) (v : Fin k → Fin G.n) :
    {h : (glue L lam J F σ).V → Fin G.n // (glue L lam J F σ).IsHom G h ∧
        h ∘ (glue L lam J F σ).lab = v} ≃
      Σ g : {g : L → Fin G.n // g ∘ lam = v},
        ∀ j, {h : (F j).V → Fin G.n // (F j).IsHom G h ∧ h ∘ (F j).lab = g.1 ∘ σ j} where
  toFun h := ⟨⟨fun l => h.1 (.inl l), h.2.2⟩, fun j => ⟨fun x => h.1 (.inr ⟨j, x⟩),
    ⟨fun x y hxy => h.2.1.1 _ _ ⟨j, x, y, hxy, rfl, rfl⟩,
      fun x c hx => h.2.1.2.1 _ _ ⟨j, x, hx, rfl⟩,
      fun x y hxy => h.2.1.2.2 _ _ (Or.inl ⟨j, x, y, hxy, rfl, rfl⟩)⟩,
    funext fun i => h.2.1.2.2 _ _ (Or.inr ⟨j, i, rfl, rfl⟩)⟩⟩
  invFun p := ⟨Sum.elim p.1.1 (fun q => (p.2 q.1).1 q.2),
    ⟨by
      rintro _ _ ⟨j, x, y, hxy, rfl, rfl⟩
      exact (p.2 j).2.1.1 x y hxy,
    by
      rintro _ c ⟨j, x, hx, rfl⟩
      exact (p.2 j).2.1.2.1 x c hx,
    by
      rintro _ _ (⟨j, x, y, hxy, rfl, rfl⟩ | ⟨j, i, rfl, rfl⟩)
      · exact (p.2 j).2.1.2.2 x y hxy
      · exact congrFun (p.2 j).2.2 i⟩,
    p.1.2⟩
  left_inv h := by
    apply Subtype.ext
    funext a
    rcases a with l | ⟨j, x⟩ <;> rfl
  right_inv p := rfl

lemma tensor_glue [DecidableEq L] (G : ColoredGraph) (v : Fin k → Fin G.n) :
    (glue L lam J F σ).tensor G v =
      ∑ g : L → Fin G.n, if g ∘ lam = v then ∏ j, (F j).tensor G (g ∘ σ j) else 0 := by
  classical
  unfold tensor
  rw [Nat.card_congr (glueHomEquiv L lam J F σ G v), Nat.card_sigma]
  simp_rw [Nat.card_pi]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (fun g => by simp)
    (fun g => ∏ j, Nat.card {h // (F j).IsHom G h ∧ h ∘ (F j).lab = g ∘ σ j})).symm

lemma liftEqvGen (j : J) {x y : (F j).V} (h : EqvGen (F j).eqv x y) :
    EqvGen (glue L lam J F σ).eqv (.inr ⟨j, x⟩) (.inr ⟨j, y⟩) := by
  induction h with
  | rel x y h => exact EqvGen.rel _ _ (Or.inl ⟨j, x, y, h, rfl, rfl⟩)
  | refl => exact EqvGen.refl _
  | symm _ _ _ ih => exact EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact EqvGen.trans _ _ _ ih1 ih2

lemma small_glue (N : J → ℕ) (hF : ∀ j, (F j).Small (N j)) :
    (glue L lam J F σ).Small (Nat.card {l : L // l ∉ Set.range lam} + ∑ j, N j) := by
  classical
  choose W g hW hc hg using hF
  let gg : {l : L // l ∉ Set.range lam} ⊕ (Σ j, W j) → (glue L lam J F σ).V :=
    Sum.elim (fun l => Sum.inl l.1) (fun p => Sum.inr ⟨p.1, g p.1 p.2⟩)
  refine ⟨{l : L // l ∉ Set.range lam} ⊕ Σ j, W j, gg, inferInstance, ?_, ?_⟩
  · rw [Nat.card_sum, Nat.card_sigma]
    exact Nat.add_le_add_left (Finset.sum_le_sum fun j _ => hc j) _
  · -- vertices of `L`
    have hL : ∀ l : L, (∃ i, EqvGen (glue L lam J F σ).eqv (.inl l) (.inl (lam i))) ∨
        ∃ w, EqvGen (glue L lam J F σ).eqv (.inl l) (gg w) := by
      intro l
      by_cases hl : l ∈ Set.range lam
      · obtain ⟨i, rfl⟩ := hl
        exact Or.inl ⟨i, EqvGen.refl _⟩
      · exact Or.inr ⟨.inl ⟨l, hl⟩, EqvGen.refl _⟩
    rintro (l | ⟨j, x⟩)
    · exact hL l
    · rcases hg j x with ⟨i, hi⟩ | ⟨w, hw⟩
      · have h1 := liftEqvGen L lam J F σ j hi
        have h2 : EqvGen (glue L lam J F σ).eqv (.inr ⟨j, (F j).lab i⟩) (.inl (σ j i)) :=
          EqvGen.rel _ _ (Or.inr ⟨j, i, rfl, rfl⟩)
        rcases hL (σ j i) with ⟨i', h3⟩ | ⟨w, h3⟩
        · exact Or.inl ⟨i', (h1.trans _ _ _ h2).trans _ _ _ h3⟩
        · exact Or.inr ⟨w, (h1.trans _ _ _ h2).trans _ _ _ h3⟩
      · exact Or.inr ⟨.inr ⟨j, w⟩, liftEqvGen L lam J F σ j hw⟩

/-- The embedding of the `j`-th part into a glued graph. -/
def inrEmb (j : J) : (F j).V ↪ (glue L lam J F σ).V :=
  ⟨fun x => Sum.inr ⟨j, x⟩, fun x y h => by
    have h' := Sum.inr_injective h
    exact eq_of_heq (Sigma.mk.inj_iff.1 h').2⟩

/-- The embedding of the fresh vertices into a glued graph. -/
def inlEmb : L ↪ (glue L lam J F σ).V := ⟨Sum.inl, Sum.inl_injective⟩

open scoped Classical in
/-- The bag tree of a glued graph: a root bag `L` with the trees of the parts below. -/
noncomputable def glueTree (D : ∀ j, (F j).Decomp) : BagTree (glue L lam J F σ).V where
  I := Option (Σ j, (D j).T.I)
  root := none
  parent t := t.elim none fun p =>
    if p.2 = (D p.1).T.root then none else some ⟨p.1, (D p.1).T.parent p.2⟩
  depth t := t.elim 0 fun p => (D p.1).T.depth p.2 + 1
  depth_lt := by
    rintro (_ | ⟨j, t⟩) ht
    · exact absurd rfl ht
    · simp only [Option.elim_some]
      split_ifs with h
      · simp
      · simpa using (D j).T.depth_lt t h
  bag t := t.elim (Finset.univ.map (inlEmb L lam J F σ)) fun p =>
    ((D p.1).T.bag p.2).map (inrEmb L lam J F σ p.1)

variable {L lam J F σ}

lemma glueTree_root (D : ∀ j, (F j).Decomp) : (glueTree L lam J F σ D).root = none := rfl

open scoped Classical in
lemma glueTree_parent_some (D : ∀ j, (F j).Decomp) (j : J) (t : (D j).T.I) :
    (glueTree L lam J F σ D).parent (some ⟨j, t⟩) =
      if t = (D j).T.root then none else some ⟨j, (D j).T.parent t⟩ := rfl

lemma glueTree_bag_none (D : ∀ j, (F j).Decomp) :
    (glueTree L lam J F σ D).bag none = Finset.univ.map (inlEmb L lam J F σ) := rfl

lemma glueTree_bag_some (D : ∀ j, (F j).Decomp) (p : Σ j, (D j).T.I) :
    (glueTree L lam J F σ D).bag (some p) = ((D p.1).T.bag p.2).map (inrEmb L lam J F σ p.1) :=
  rfl

lemma mem_glueTree_none (D : ∀ j, (F j).Decomp) (a : (glue L lam J F σ).V) :
    a ∈ (glueTree L lam J F σ D).bag none ↔ ∃ l, a = .inl l := by
  rw [glueTree_bag_none, Finset.mem_map]
  constructor
  · rintro ⟨l, -, h⟩
    exact ⟨l, h.symm⟩
  · rintro ⟨l, h⟩
    exact ⟨l, Finset.mem_univ _, h.symm⟩

lemma inr_mem_glueTree_some (D : ∀ j, (F j).Decomp) (j j' : J) (x : (F j).V)
    (t : (D j').T.I) :
    inrEmb L lam J F σ j x ∈ (glueTree L lam J F σ D).bag (some ⟨j', t⟩) ↔
      ∃ h : j' = j, x ∈ (D j).T.bag (h ▸ t) := by
  rw [glueTree_bag_some, Finset.mem_map]
  constructor
  · rintro ⟨y, hy, h⟩
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 (Sum.inr_injective h)
    cases h
    exact ⟨rfl, hy⟩
  · rintro ⟨rfl, h⟩
    exact ⟨x, h, rfl⟩

lemma inl_not_mem_glueTree_some (D : ∀ j, (F j).Decomp) (l : L) (p : Σ j, (D j).T.I) :
    inlEmb L lam J F σ l ∉ (glueTree L lam J F σ D).bag (some p) := by
  rw [glueTree_bag_some, Finset.mem_map]
  rintro ⟨y, -, h⟩
  cases h

lemma mem_glueTree_some (D : ∀ j, (F j).Decomp) (j : J) (x : (F j).V) (t : (D j).T.I) :
    inrEmb L lam J F σ j x ∈ (glueTree L lam J F σ D).bag (some ⟨j, t⟩) ↔
      x ∈ (D j).T.bag t := by
  rw [inr_mem_glueTree_some]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨rfl, h⟩⟩

lemma isTop_glueTree (D : ∀ j, (F j).Decomp) (j : J) (x : (F j).V) (t : (D j).T.I) :
    (glueTree L lam J F σ D).IsTop (inrEmb L lam J F σ j x) (some ⟨j, t⟩) ↔
      (D j).T.IsTop x t := by
  classical
  unfold BagTree.IsTop
  rw [glueTree_parent_some, mem_glueTree_some D j x t, glueTree_root]
  by_cases ht : t = (D j).T.root
  · have hn : inrEmb L lam J F σ j x ∉ (glueTree L lam J F σ D).bag none := by
      rw [mem_glueTree_none]
      rintro ⟨l, hl⟩
      have e : inrEmb L lam J F σ j x = Sum.inr ⟨j, x⟩ := rfl
      rw [e] at hl
      cases hl
    simp only [ht, if_true, hn, not_false_eq_true, or_true, true_or]
  · simp only [ht, if_false, reduceCtorEq, false_or, mem_glueTree_some]

/-- The decomposition of a glued graph. -/
noncomputable def glueDecomp (D : ∀ j, (F j).Decomp) (hL : Fintype.card L ≤ k + 1) :
    (glue L lam J F σ).Decomp where
  T := glueTree L lam J F σ D
  valid := by
    classical
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro (l | ⟨j, x⟩)
      · exact ⟨none, (mem_glueTree_none D _).2 ⟨l, rfl⟩⟩
      · obtain ⟨t, ht⟩ := (D j).valid.cover x
        exact ⟨some ⟨j, t⟩, (mem_glueTree_some D j x t).2 ht⟩
    · rintro _ _ ⟨j, x, y, hxy, rfl, rfl⟩
      obtain ⟨t, hx, hy⟩ := (D j).valid.edge x y hxy
      exact ⟨some ⟨j, t⟩, (mem_glueTree_some D j x t).2 hx, (mem_glueTree_some D j y t).2 hy⟩
    · rintro _ _ (⟨j, x, y, hxy, rfl, rfl⟩ | ⟨j, i, rfl, rfl⟩)
      · obtain ⟨t, s, hx, hy, h⟩ := (D j).valid.eqv x y hxy
        refine ⟨some ⟨j, t⟩, some ⟨j, s⟩, (mem_glueTree_some D j x t).2 hx,
          (mem_glueTree_some D j y s).2 hy, ?_⟩
        rcases h with rfl | ⟨hne, rfl⟩
        · exact Or.inl rfl
        · refine Or.inr ⟨by rw [glueTree_root]; exact Option.some_ne_none _, ?_⟩
          rw [glueTree_parent_some, if_neg hne]
      · refine ⟨some ⟨j, (D j).T.root⟩, none, (mem_glueTree_some D j _ _).2 ((D j).root_lab i),
          (mem_glueTree_none D _).2 ⟨_, rfl⟩, Or.inr ⟨by rw [glueTree_root]; exact Option.some_ne_none _, ?_⟩⟩
        rw [glueTree_parent_some, if_pos rfl]
    · rintro (l | ⟨j, x⟩) t s ht hs
      · have key : ∀ u, (glueTree L lam J F σ D).IsTop (.inl l) u → u = none := by
          rintro (_ | p) ⟨hu, -⟩
          · rfl
          · exact absurd hu (inl_not_mem_glueTree_some D l p)
        rw [key t ht, key s hs]
      · have key : ∀ u, (glueTree L lam J F σ D).IsTop (.inr ⟨j, x⟩) u →
            ∃ t', u = some ⟨j, t'⟩ ∧ (D j).T.IsTop x t' := by
          rintro (_ | ⟨j', u⟩) hu
          · obtain ⟨l, hl⟩ := (mem_glueTree_none D _).1 hu.1
            cases hl
          · obtain ⟨h, -⟩ := (inr_mem_glueTree_some D j j' x u).1 hu.1
            subst j'
            exact ⟨u, rfl, (isTop_glueTree D j x u).1 hu⟩
        obtain ⟨t', rfl, ht'⟩ := key t ht
        obtain ⟨s', rfl, hs'⟩ := key s hs
        rw [(D j).valid.top x t' s' ht' hs']
  width := by
    rintro (_ | ⟨j, t⟩)
    · rw [glueTree_bag_none, Finset.card_map, Finset.card_univ]
      exact hL
    · rw [glueTree_bag_some, Finset.card_map]
      exact (D j).width t
  root_lab i := (mem_glueTree_none D _).2 ⟨_, rfl⟩

lemma good_glue (N : J → ℕ) (hF : ∀ j, (F j).Good (N j)) (hL : Fintype.card L ≤ k + 1) :
    (glue L lam J F σ).Good (Nat.card {l : L // l ∉ Set.range lam} + ∑ j, N j) :=
  ⟨⟨glueDecomp (fun j => (hF j).1.some) hL⟩, small_glue L lam J F σ N fun j => (hF j).2⟩

end Glue

end LGraph

end Lax119563Proofs.HomTensors

end HomTensors_LGraph

/-! ### Formerly `Lax119563Proofs.HomTensors.PolyClosure` -/

section HomTensors_PolyClosure

/-!
# Polynomial closure

Lemma `lem:polynomial-closure`: for a finite set `𝒢` of functions on a finite set `X` of size
`M`, every function that is constant on the classes of "agreeing on all of `𝒢`" is a linear
combination of products of at most `M - 1` elements of `𝒢`.

The span `P d` of the products of at most `d` elements forms an increasing chain that is
constant from the first `d` with `P (d+1) = P d` on; as `dim P 0 = 1` and `dim P d ≤ M`, the
chain is constant from `M - 1` on, so `P (M-1)` is closed under multiplication with `𝒢`, and
Lagrange-type interpolation products give all class indicators.
-/

namespace Lax119563Proofs.HomTensors

open Finset

variable {X : Type}

/-- Products of at most `d` elements of `𝒢`. -/
def prods (𝒢 : Set (X → ℚ)) (d : ℕ) : Set (X → ℚ) :=
  {f | ∃ l : List (X → ℚ), l.length ≤ d ∧ (∀ g ∈ l, g ∈ 𝒢) ∧ l.prod = f}

/-- The span of the products of at most `d` elements of `𝒢`. -/
noncomputable def polySpan (𝒢 : Set (X → ℚ)) (d : ℕ) : Submodule ℚ (X → ℚ) :=
  Submodule.span ℚ (prods 𝒢 d)

variable (𝒢 : Set (X → ℚ))

lemma polySpan_mono {d e : ℕ} (h : d ≤ e) : polySpan 𝒢 d ≤ polySpan 𝒢 e := by
  apply Submodule.span_mono
  rintro f ⟨l, hl, hg, rfl⟩
  exact ⟨l, hl.trans h, hg, rfl⟩

lemma one_mem_polySpan (d : ℕ) : (1 : X → ℚ) ∈ polySpan 𝒢 d :=
  Submodule.subset_span ⟨[], by simp, by simp, rfl⟩

lemma mul_mem_polySpan {g : X → ℚ} (hg : g ∈ 𝒢) {d : ℕ} {f : X → ℚ} (hf : f ∈ polySpan 𝒢 d) :
    g * f ∈ polySpan 𝒢 (d + 1) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l, hl, hl', rfl⟩ := hf
    exact Submodule.subset_span ⟨g :: l, by simpa using hl, by
      rintro g' (_ | ⟨_, hg'⟩)
      · exact hg
      · exact hl' g' hg', rfl⟩
  | zero => simp
  | add f f' _ _ h h' => rw [mul_add]; exact Submodule.add_mem _ h h'
  | smul c f _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h

lemma polySpan_step {d : ℕ} (h : polySpan 𝒢 (d + 1) ≤ polySpan 𝒢 d) :
    polySpan 𝒢 (d + 2) ≤ polySpan 𝒢 (d + 1) := by
  apply Submodule.span_le.2
  rintro f ⟨l, hl, hg, rfl⟩
  cases l with
  | nil => exact one_mem_polySpan 𝒢 _
  | cons g l =>
    rw [List.prod_cons]
    apply mul_mem_polySpan 𝒢 (hg g (by simp))
    apply h
    exact Submodule.subset_span ⟨l, by simpa using hl, fun g' hg' => hg g' (by simp [hg']), rfl⟩

lemma polySpan_stable {d : ℕ} (h : polySpan 𝒢 (d + 1) ≤ polySpan 𝒢 d) (e : ℕ) :
    polySpan 𝒢 (d + e) ≤ polySpan 𝒢 d := by
  have step : ∀ e, polySpan 𝒢 (d + e + 1) ≤ polySpan 𝒢 (d + e) := by
    intro e
    induction e with
    | zero => simpa using h
    | succ e ih => exact polySpan_step 𝒢 ih
  induction e with
  | zero => simp
  | succ e ih => exact (step e).trans ih

lemma exists_polySpan_stable [Fintype X] [Nonempty X] :
    ∃ d, d + 1 ≤ Fintype.card X ∧ polySpan 𝒢 (d + 1) ≤ polySpan 𝒢 d := by
  by_contra hcon
  push Not at hcon
  have hlt : ∀ d, d + 1 ≤ Fintype.card X → polySpan 𝒢 d < polySpan 𝒢 (d + 1) :=
    fun d hd => lt_of_le_not_ge (polySpan_mono 𝒢 (Nat.le_succ d)) (hcon d hd)
  have hrank : ∀ d, d ≤ Fintype.card X → d + 1 ≤ Module.finrank ℚ (polySpan 𝒢 d) := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [zero_add, Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
      intro h0
      have := one_mem_polySpan 𝒢 0
      rw [h0, Submodule.mem_bot] at this
      exact one_ne_zero this
    | succ d ih =>
      intro hd
      have := Submodule.finrank_lt_finrank_of_lt (hlt d hd)
      have := ih (by omega)
      omega
  have h1 := hrank _ le_rfl
  have h2 := Submodule.finrank_le (polySpan 𝒢 (Fintype.card X))
  rw [Module.finrank_fintype_fun_eq_card] at h2
  omega

/-- The span `polySpan 𝒢 (|X| - 1)` is closed under multiplication with elements of `𝒢`. -/
lemma mul_mem_polySpan_top [Fintype X] {g : X → ℚ} (hg : g ∈ 𝒢) {f : X → ℚ}
    (hf : f ∈ polySpan 𝒢 (Fintype.card X - 1)) : g * f ∈ polySpan 𝒢 (Fintype.card X - 1) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · rw [Subsingleton.elim (g * f) 0]
    exact Submodule.zero_mem _
  obtain ⟨d, hd, hst⟩ := exists_polySpan_stable 𝒢
  have h := mul_mem_polySpan 𝒢 hg hf
  have hM : Fintype.card X - 1 + 1 = d + (Fintype.card X - d) := by omega
  rw [hM] at h
  exact polySpan_mono 𝒢 (by omega) (polySpan_stable 𝒢 hst _ h)

lemma prod_mul_mem {A : Submodule ℚ (X → ℚ)} {ι : Type} (s : Finset ι) (φ : ι → X → ℚ)
    (hφ : ∀ i ∈ s, ∀ f ∈ A, φ i * f ∈ A) : ∀ f ∈ A, (∏ i ∈ s, φ i) * f ∈ A := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    intro f hf
    rw [prod_insert ha, mul_assoc]
    exact hφ a (mem_insert_self a s) _
      (ih (fun i hi => hφ i (mem_insert_of_mem hi)) f hf)

/-- **Polynomial closure.** A function constant on the classes of agreement on the finite set
`𝒢` is a linear combination of products of at most `|X| - 1` elements of `𝒢`. -/
theorem mem_polySpan [Fintype X] (𝒢 : Finset (X → ℚ)) (f : X → ℚ)
    (hf : ∀ x y, (∀ g ∈ 𝒢, g x = g y) → f x = f y) :
    f ∈ polySpan (𝒢 : Set (X → ℚ)) (Fintype.card X - 1) := by
  classical
  set A := polySpan (𝒢 : Set (X → ℚ)) (Fintype.card X - 1)
  -- interpolation factors
  let φ : (X → ℚ) → X → X → X → ℚ := fun g x₀ x => (g x₀ - g x)⁻¹ • (g - fun _ => g x)
  have hφ : ∀ g ∈ 𝒢, ∀ x₀ x, ∀ f ∈ A, φ g x₀ x * f ∈ A := by
    intro g hg x₀ x f hf
    have : φ g x₀ x * f = (g x₀ - g x)⁻¹ • (g * f - g x • f) := by
      funext z
      simp [φ, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (mul_mem_polySpan_top _ hg hf)
      (Submodule.smul_mem _ _ hf))
  let e : X → X → ℚ := fun x₀ =>
    ∏ g ∈ 𝒢, ∏ x ∈ univ.filter (fun x => g x ≠ g x₀), φ g x₀ x
  have he_mem : ∀ x₀, e x₀ ∈ A := by
    intro x₀
    have := prod_mul_mem 𝒢 (fun g => ∏ x ∈ univ.filter (fun x => g x ≠ g x₀), φ g x₀ x)
      (fun g hg => prod_mul_mem _ _ (fun x _ => hφ g hg x₀ x)) 1
      (one_mem_polySpan _ _)
    simpa [e] using this
  have he_apply : ∀ x₀ z, e x₀ z = if ∀ g ∈ 𝒢, g z = g x₀ then 1 else 0 := by
    intro x₀ z
    simp only [e, Finset.prod_apply]
    split_ifs with h
    · refine Finset.prod_eq_one fun g hg => Finset.prod_eq_one fun x hx => ?_
      have hx : g x ≠ g x₀ := (Finset.mem_filter.1 hx).2
      simp only [φ, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, h g hg]
      exact inv_mul_cancel₀ (sub_ne_zero.2 hx.symm)
    · push Not at h
      obtain ⟨g, hg, hgz⟩ := h
      refine Finset.prod_eq_zero hg (Finset.prod_eq_zero (i := z) (by simp [hgz]) ?_)
      simp [φ]
  -- the class sizes
  let N : X → ℕ := fun z => (univ.filter fun y => ∀ g ∈ 𝒢, g y = g z).card
  have hf_eq : f = ∑ x₀, (f x₀ / N x₀) • e x₀ := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, he_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero]
    rw [← Finset.sum_filter]
    have hfil : (univ.filter fun x₀ : X => ∀ g ∈ 𝒢, g z = g x₀) =
        univ.filter fun y => ∀ g ∈ 𝒢, g y = g z := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h g hg => (h g hg).symm, fun h g hg => (h g hg).symm⟩
    have hterm : ∀ x₀ ∈ (univ.filter fun x₀ : X => ∀ g ∈ 𝒢, g z = g x₀),
        f x₀ / N x₀ = f z / N z := by
      intro x₀ hx₀
      have hx₀ := (Finset.mem_filter.1 hx₀).2
      rw [hf x₀ z fun g hg => (hx₀ g hg).symm]
      congr 2
      simp only [N]
      congr 1
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h g hg => (h g hg).trans (hx₀ g hg).symm,
        fun h g hg => (h g hg).trans (hx₀ g hg)⟩
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, hfil, nsmul_eq_mul]
    have hpos : (N z : ℚ) ≠ 0 := by
      have : 0 < N z := Finset.card_pos.2 ⟨z, by simp⟩
      exact_mod_cast this.ne'
    field_simp
    rfl
  rw [hf_eq]
  exact Submodule.sum_mem _ fun x₀ _ => Submodule.smul_mem _ _ (he_mem x₀)

end Lax119563Proofs.HomTensors

end HomTensors_PolyClosure

/-! ### Formerly `Lax119563Proofs.HomTensors.Spaces` -/

section HomTensors_Spaces

/-!
# The spaces `𝒱_N` of homomorphism tensors

For colored graphs `G, H` let `Tup k G H = V(G)^k ⊔ V(H)^k`. The tensor of a labeled graph is
the concatenation of its homomorphism tensors on `G` and on `H`. `Vs G H N` is the span of the
tensors of good labeled graphs with at most `N` vertices besides the labels. It contains the
constant `1`, is closed under products (gluing: `Vs a * Vs b ≤ Vs (a + b)`), and under the
extension operator (`extOp` maps `Vs N ^ k` into `Vs (1 + k N)`).
-/

namespace Lax119563Proofs.HomTensors

open Lax119563.ColoredGraphs LGraph Finset

variable {k : ℕ} (G H : ColoredGraph)

/-- The `k`-tuples of `G` and of `H`. -/
abbrev Tup (k : ℕ) (G H : ColoredGraph) := (Fin k → Fin G.n) ⊕ (Fin k → Fin H.n)

/-- The tensor of a labeled graph on `Tup k G H`. -/
noncomputable def tens (F : LGraph k) : Tup k G H → ℚ :=
  Sum.elim (fun v => (F.tensor G v : ℚ)) (fun v => (F.tensor H v : ℚ))

/-- Tensors of good labeled graphs. -/
def tset (N : ℕ) : Set (Tup k G H → ℚ) := {f | ∃ F : LGraph k, F.Good N ∧ tens G H F = f}

/-- The span `𝒱_N`. -/
noncomputable def Vs (N : ℕ) : Submodule ℚ (Tup k G H → ℚ) := Submodule.span ℚ (tset G H N)

variable {G H}

lemma Vs_mono {N N' : ℕ} (h : N ≤ N') : Vs (k := k) G H N ≤ Vs G H N' :=
  Submodule.span_mono (by rintro f ⟨F, hF, rfl⟩; exact ⟨F, hF.mono h, rfl⟩)

lemma tens_mem {N : ℕ} {F : LGraph k} (hF : F.Good N) : tens G H F ∈ Vs G H N :=
  Submodule.subset_span ⟨F, hF, rfl⟩

/-! ### Atoms -/

open scoped Classical in
lemma tens_atom_inl (adj : Fin k → Fin k → Prop) (pred : Fin k → ℕ → Prop)
    (eqv : Fin k → Fin k → Prop) (v : Fin k → Fin G.n) :
    tens G H (atom adj pred eqv) (.inl v) = if (atom adj pred eqv).IsHom G v then 1 else 0 := by
  simp only [tens, Sum.elim_inl, tensor_atom]
  split_ifs <;> simp

open scoped Classical in
lemma tens_atom_inr (adj : Fin k → Fin k → Prop) (pred : Fin k → ℕ → Prop)
    (eqv : Fin k → Fin k → Prop) (v : Fin k → Fin H.n) :
    tens G H (atom adj pred eqv) (.inr v) = if (atom adj pred eqv).IsHom H v then 1 else 0 := by
  simp only [tens, Sum.elim_inr, tensor_atom]
  split_ifs <;> simp

lemma one_mem_Vs : (1 : Tup k G H → ℚ) ∈ Vs G H 0 := by
  have h := tens_mem (G := G) (H := H) (good_atom (k := k) (fun _ _ => False) (fun _ _ => False)
    (fun _ _ => False))
  convert h using 1
  funext x
  rcases x with v | v
  · rw [tens_atom_inl, if_pos (by simp [atom, IsHom])]; rfl
  · rw [tens_atom_inr, if_pos (by simp [atom, IsHom])]; rfl

/-! ### Products -/

/-- Gluing two labeled graphs along their labels. -/
def mul (F₁ F₂ : LGraph k) : LGraph k :=
  glue (Fin k) id Bool (fun b => cond b F₁ F₂) (fun _ => id)

lemma tensor_mul (F₁ F₂ : LGraph k) (G : ColoredGraph) (v : Fin k → Fin G.n) :
    (mul F₁ F₂).tensor G v = F₁.tensor G v * F₂.tensor G v := by
  rw [mul, tensor_glue]
  simp [Function.comp_id, Fintype.prod_bool]

lemma good_mul {F₁ F₂ : LGraph k} {a b : ℕ} (h₁ : F₁.Good a) (h₂ : F₂.Good b) :
    (mul F₁ F₂).Good (a + b) := by
  have := good_glue (L := Fin k) (lam := id) (J := Bool) (F := fun b => cond b F₁ F₂)
    (σ := fun _ => id) (fun c => cond c a b) (by rintro (_ | _) <;> assumption)
    (by simp)
  refine this.mono (le_of_eq ?_)
  have : Nat.card {l : Fin k // l ∉ Set.range (id : Fin k → Fin k)} = 0 := by
    rw [Nat.card_eq_zero]; left; exact ⟨fun ⟨l, hl⟩ => hl ⟨l, rfl⟩⟩
  simp [this, Fintype.sum_bool, add_comm]

lemma tens_mul (F₁ F₂ : LGraph k) : tens G H (mul F₁ F₂) = tens G H F₁ * tens G H F₂ := by
  funext x
  rcases x with v | v <;> simp [tens, tensor_mul]

lemma Vs_mul (a b : ℕ) : Vs (k := k) G H a * Vs G H b ≤ Vs G H (a + b) := by
  rw [Vs, Vs, Submodule.span_mul_span]
  apply Submodule.span_le.2
  rintro _ ⟨_, ⟨F₁, h₁, rfl⟩, _, ⟨F₂, h₂, rfl⟩, rfl⟩
  show tens G H F₁ * tens G H F₂ ∈ _
  rw [← tens_mul]
  exact tens_mem (good_mul h₁ h₂)

lemma list_prod_mem (a : ℕ) (l : List (Tup k G H → ℚ)) (hl : ∀ g ∈ l, g ∈ Vs G H a) :
    l.prod ∈ Vs G H (l.length * a) := by
  induction l with
  | nil => simpa using one_mem_Vs
  | cons g l ih =>
    rw [List.prod_cons, List.length_cons, add_mul, one_mul, add_comm]
    exact Vs_mul _ _ (Submodule.mul_mem_mul (hl g (by simp))
      (ih fun g' hg' => hl g' (by simp [hg'])))

lemma polySpan_le_Vs (𝒢 : Set (Tup k G H → ℚ)) (a d : ℕ)
    (h𝒢 : 𝒢 ⊆ (Vs (k := k) G H a : Set (Tup k G H → ℚ))) :
    polySpan 𝒢 d ≤ Vs G H (d * a) := by
  apply Submodule.span_le.2
  rintro _ ⟨l, hl, hg, rfl⟩
  exact Vs_mono (Nat.mul_le_mul_right a hl) (list_prod_mem a l fun g hg' => h𝒢 (hg g hg'))

/-! ### Extension -/

/-- The extension operator: `v ↦ ∑_x ∏_j f_j(v[x/j])`. -/
noncomputable def extOp (f : Fin k → Tup k G H → ℚ) : Tup k G H → ℚ :=
  Sum.elim (fun p => ∑ q, ∏ j, f j (.inl (Function.update p j q)))
    (fun p => ∑ q, ∏ j, f j (.inr (Function.update p j q)))

/-- Extension of `k` labeled graphs: a fresh vertex `w = none`, labels `b_i = some i`; the
`j`-th label of `F j` is glued to `w`, its other labels `i` to `b_i`. -/
def extG (F : Fin k → LGraph k) : LGraph k :=
  glue (Option (Fin k)) some (Fin k) F (fun j i => if i = j then none else some i)

lemma tensor_extG (F : Fin k → LGraph k) (G : ColoredGraph) (v : Fin k → Fin G.n) :
    (extG F).tensor G v = ∑ q, ∏ j, (F j).tensor G (Function.update v j q) := by
  classical
  rw [extG, tensor_glue]
  rw [← (Equiv.piOptionEquivProd (β := fun _ => Fin G.n)).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hc : ∀ w : Fin k → Fin G.n,
      ((Equiv.piOptionEquivProd (β := fun _ => Fin G.n)).symm (q, w)) ∘ some = w := by
    intro w; funext i; rfl
  simp only [hc]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  funext i
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

lemma good_extG {F : Fin k → LGraph k} {N : ℕ} (hF : ∀ j, (F j).Good N) :
    (extG F).Good (1 + k * N) := by
  have := good_glue (L := Option (Fin k)) (lam := some) (J := Fin k) (F := F)
    (σ := fun j i => if i = j then none else some i) (fun _ => N) hF (by simp)
  refine this.mono (le_of_eq ?_)
  have : Nat.card {l : Option (Fin k) // l ∉ Set.range some} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨none, by simp⟩, ?_⟩
    rintro ⟨_ | l, hl⟩
    · rfl
    · exact absurd ⟨l, rfl⟩ hl
  rw [this]
  simp

lemma tens_extG (F : Fin k → LGraph k) :
    tens G H (extG F) = extOp (fun j => tens G H (F j)) := by
  funext x
  rcases x with v | v <;> simp [tens, extOp, tensor_extG]

lemma prod_update_apply {Y : Type} (f : Fin k → Y → ℚ) (j : Fin k) (x : Y → ℚ)
    (pt : Fin k → Y) :
    ∏ i, (Function.update f j x i) (pt i) = x (pt j) * ∏ i ∈ univ.erase j, f i (pt i) := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

lemma extOp_update_add (f : Fin k → Tup k G H → ℚ) (j : Fin k) (x y : Tup k G H → ℚ) :
    extOp (Function.update f j (x + y)) =
      extOp (Function.update f j x) + extOp (Function.update f j y) := by
  funext z
  rcases z with p | p <;>
  · simp only [extOp, Sum.elim_inl, Sum.elim_inr, Pi.add_apply]
    simp only [prod_update_apply (Y := Tup k G H) f j _
      (fun i => _), Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma extOp_update_smul (f : Fin k → Tup k G H → ℚ) (j : Fin k) (c : ℚ) (x : Tup k G H → ℚ) :
    extOp (Function.update f j (c • x)) = c • extOp (Function.update f j x) := by
  funext z
  rcases z with p | p <;>
  · simp only [extOp, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul]
    simp only [prod_update_apply (Y := Tup k G H) f j _
      (fun i => _), Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- A map that is additive and homogeneous in each argument sends a family of spans into a
submodule as soon as it does so for the generators. -/
lemma multilinear_mem {ι M N : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M]
    [Module ℚ M] [AddCommGroup N] [Module ℚ N] (Φ : (ι → M) → N)
    (hadd : ∀ f j x y, Φ (Function.update f j (x + y)) =
      Φ (Function.update f j x) + Φ (Function.update f j y))
    (hsmul : ∀ f j (c : ℚ) x, Φ (Function.update f j (c • x)) = c • Φ (Function.update f j x))
    (S : ι → Set M) (V : Submodule ℚ N) (hS : ∀ f, (∀ j, f j ∈ S j) → Φ f ∈ V)
    (f : ι → M) (hf : ∀ j, f j ∈ Submodule.span ℚ (S j)) : Φ f ∈ V := by
  have key : ∀ s : Finset ι, ∀ f : ι → M, (∀ j ∈ s, f j ∈ Submodule.span ℚ (S j)) →
      (∀ j ∉ s, f j ∈ S j) → Φ f ∈ V := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun f _ h => hS f fun j => h j (Finset.notMem_empty j)
    | insert a s ha ih =>
      intro f h₁ h₂
      let U : Submodule ℚ M :=
        { carrier := {x | Φ (Function.update f a x) ∈ V}
          add_mem' := fun {x y} hx hy => by
            simp only [Set.mem_ofPred_eq, hadd] at *
            exact V.add_mem hx hy
          zero_mem' := by
            simp only [Set.mem_ofPred_eq]
            have := hsmul f a 0 0
            rw [zero_smul, zero_smul] at this
            rw [this]
            exact V.zero_mem
          smul_mem' := fun c x hx => by
            simp only [Set.mem_ofPred_eq, hsmul] at *
            exact V.smul_mem c hx }
      have hU : Submodule.span ℚ (S a) ≤ U := by
        apply Submodule.span_le.2
        intro x hx
        show Φ (Function.update f a x) ∈ V
        apply ih
        · intro j hj
          rw [Function.update_of_ne (by rintro rfl; exact ha hj)]
          exact h₁ j (Finset.mem_insert_of_mem hj)
        · intro j hj
          by_cases hja : j = a
          · subst hja; simpa using hx
          · rw [Function.update_of_ne hja]
            exact h₂ j (by simp [hja, hj])
      have hfa : f a ∈ U := hU (h₁ a (Finset.mem_insert_self a s))
      have : Φ (Function.update f a (f a)) ∈ V := hfa
      rwa [Function.update_eq_self] at this
  exact key univ f (fun j _ => hf j) (fun j hj => absurd (mem_univ j) hj)

lemma extOp_mem {N : ℕ} (f : Fin k → Tup k G H → ℚ) (hf : ∀ j, f j ∈ Vs G H N) :
    extOp f ∈ Vs G H (1 + k * N) := by
  classical
  refine multilinear_mem extOp extOp_update_add extOp_update_smul (fun _ => tset G H N) _ ?_ f hf
  intro f hf
  choose F hF hFf using hf
  have : f = fun j => tens G H (F j) := funext fun j => (hFf j).symm
  rw [this, ← tens_extG]
  exact tens_mem (good_extG hF)

end Lax119563Proofs.HomTensors

end HomTensors_Spaces

/-! ### Formerly `Lax119563Proofs.HomTensors.Rounds` -/

section HomTensors_Rounds

/-!
# Color-class indicators of `k`-WL lie in `𝒱`

With `M = |V(G)|^k + |V(H)|^k` and `ν_0 = 0`, `ν_{r+1} = (M - 1)(1 + k ν_r)`, every
color-class indicator of round `r` lies in `Vs G H ν_r`.

* Round zero: the atomic type is a function of the values of the atom tensors
  `[v_i = v_j]`, `[v_i v_j ∈ E]`, `[χ(v_i) = c]` (all in `Vs 0`), so polynomial closure applies.
* Step: the round-`r+1` color is a function of the round-`r` class indicators and of the
  extensions `N_c` of `k` class indicators, which lie in `Vs (1 + k ν_r)`.
-/

namespace Lax119563Proofs.HomTensors

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman LGraph Finset

variable {k : ℕ} {G H : ColoredGraph}

variable (G H) in
/-- The round-`r` coloring on `Tup k G H`. -/
noncomputable def chi (r : ℕ) : Tup k G H → Color k r := Sum.elim (color G r) (color H r)

open scoped Classical in
variable (G H) in
/-- The indicator of a round-`r` color class on `Tup k G H`. -/
noncomputable def ind (r : ℕ) (c : Color k r) : Tup k G H → ℚ :=
  fun x => if chi G H r x = c then 1 else 0

/-- The size bound: `ν_0 = 0`, `ν_{r+1} = (M - 1)(1 + k ν_r)`. -/
def nu (k M : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => (M - 1) * (1 + k * nu k M r)

lemma ite_one_zero_iff {p q : Prop} [Decidable p] [Decidable q]
    (h : (if p then (1 : ℚ) else 0) = if q then 1 else 0) : p ↔ q := by
  split_ifs at h with hp hq hq <;> simp_all

/-! ### Round zero -/

/-- `[v_i = v_j]`. -/
def eqAtom (i j : Fin k) : LGraph k := atom (fun _ _ => False) (fun _ _ => False)
  (fun a b => a = i ∧ b = j)

/-- `[v_i v_j ∈ E]`. -/
def adjAtom (i j : Fin k) : LGraph k := atom (fun a b => a = i ∧ b = j) (fun _ _ => False)
  (fun _ _ => False)

/-- `[χ(v_i) = c]`. -/
def colAtom (i : Fin k) (c : ℕ) : LGraph k := atom (fun _ _ => False) (fun a c' => a = i ∧ c' = c)
  (fun _ _ => False)

variable (G H) in
/-- Equality of two entries. -/
def eqF (x : Tup k G H) (i j : Fin k) : Prop := Sum.elim (fun v => v i = v j) (fun v => v i = v j) x

variable (G H) in
/-- Adjacency of two entries. -/
def adjF (x : Tup k G H) (i j : Fin k) : Prop :=
  Sum.elim (fun v => G.graph.Adj (v i) (v j)) (fun v => H.graph.Adj (v i) (v j)) x

variable (G H) in
/-- The color of an entry. -/
def colF (x : Tup k G H) (i : Fin k) : ℕ :=
  Sum.elim (fun v => G.color (v i)) (fun v => H.color (v i)) x

open scoped Classical in
lemma tens_eqAtom (i j : Fin k) (x : Tup k G H) :
    tens G H (eqAtom i j) x = if eqF G H x i j then 1 else 0 := by
  rcases x with v | v
  · rw [eqAtom, tens_atom_inl]; simp [IsHom, atom, eqF]; try (split_ifs <;> simp_all)
  · rw [eqAtom, tens_atom_inr]; simp [IsHom, atom, eqF]; try (split_ifs <;> simp_all)

open scoped Classical in
lemma tens_adjAtom (i j : Fin k) (x : Tup k G H) :
    tens G H (adjAtom i j) x = if adjF G H x i j then 1 else 0 := by
  rcases x with v | v
  · rw [adjAtom, tens_atom_inl]; simp [IsHom, atom, adjF]; try (split_ifs <;> simp_all)
  · rw [adjAtom, tens_atom_inr]; simp [IsHom, atom, adjF]; try (split_ifs <;> simp_all)

open scoped Classical in
lemma tens_colAtom (i : Fin k) (c : ℕ) (x : Tup k G H) :
    tens G H (colAtom i c) x = if colF G H x i = c then 1 else 0 := by
  rcases x with v | v
  · rw [colAtom, tens_atom_inl]; simp [IsHom, atom, colF]; try (split_ifs <;> simp_all)
  · rw [colAtom, tens_atom_inr]; simp [IsHom, atom, colF]; try (split_ifs <;> simp_all)

lemma chi_zero_eq (x : Tup k G H) (i j : Fin k) : (chi G H 0 x).eq i j = true ↔ eqF G H x i j := by
  rcases x with v | v <;> exact decide_eq_true_iff

open scoped Classical in
lemma chi_zero_adj (x : Tup k G H) (i j : Fin k) :
    (chi G H 0 x).adj i j = true ↔ adjF G H x i j := by
  rcases x with v | v <;> exact decide_eq_true_iff

lemma chi_zero_color (x : Tup k G H) (i : Fin k) : (chi G H 0 x).color i = colF G H x i := by
  rcases x with v | v <;> rfl

lemma atomicType_ext {a b : AtomicType k} (h₁ : ∀ i j, a.eq i j = b.eq i j)
    (h₂ : ∀ i j, a.adj i j = b.adj i j) (h₃ : ∀ i, a.color i = b.color i) : a = b := by
  cases a; cases b
  simp only [AtomicType.mk.injEq]
  exact ⟨funext fun i => funext fun j => h₁ i j, funext fun i => funext fun j => h₂ i j,
    funext h₃⟩

variable (G H) in
/-- The colors of `G` and `H`. -/
noncomputable def colors : Finset ℕ := by
  classical exact univ.image G.color ∪ univ.image H.color

lemma colF_mem (x : Tup k G H) (i : Fin k) : colF G H x i ∈ colors G H := by
  classical
  rcases x with v | v <;> simp [colF, colors]

variable (G H) in
open scoped Classical in
/-- The generators for round zero. -/
noncomputable def gens0 : Finset (Tup k G H → ℚ) :=
  (univ : Finset (Fin k × Fin k)).image (fun p => tens G H (eqAtom p.1 p.2)) ∪
    (univ : Finset (Fin k × Fin k)).image (fun p => tens G H (adjAtom p.1 p.2)) ∪
    (univ ×ˢ colors G H).image (fun p => tens G H (colAtom p.1 p.2))

lemma gens0_sub :
    ((gens0 G H : Finset (Tup k G H → ℚ)) : Set _) ⊆ (Vs (k := k) G H 0 : Set (Tup k G H → ℚ)) := by
  classical
  intro g hg
  simp only [gens0, coe_union, coe_image, Set.mem_union, Set.mem_image, mem_coe] at hg
  rcases hg with ((⟨p, -, rfl⟩ | ⟨p, -, rfl⟩) | ⟨p, -, rfl⟩) <;> exact tens_mem (good_atom _ _ _)

lemma chi_zero_eq_of (x y : Tup k G H) (h : ∀ g ∈ gens0 G H, g x = g y) :
    chi G H 0 x = chi G H 0 y := by
  classical
  apply atomicType_ext
  · intro i j
    have := h _ (by simp only [gens0, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_product]; exact Or.inl (Or.inl ⟨(i, j), rfl⟩))
    rw [tens_eqAtom, tens_eqAtom] at this
    have := ite_one_zero_iff this
    rw [Bool.eq_iff_iff, chi_zero_eq, chi_zero_eq]
    exact this
  · intro i j
    have := h _ (by simp only [gens0, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_product]; exact Or.inl (Or.inr ⟨(i, j), rfl⟩))
    rw [tens_adjAtom, tens_adjAtom] at this
    have := ite_one_zero_iff this
    rw [Bool.eq_iff_iff, chi_zero_adj, chi_zero_adj]
    exact this
  · intro i
    have := h (tens G H (colAtom i (colF G H x i))) (by
      simp only [gens0, mem_union, mem_image, mem_product, mem_univ, true_and]
      exact Or.inr ⟨⟨i, colF G H x i⟩, colF_mem x i, rfl⟩)
    rw [tens_colAtom, tens_colAtom] at this
    have := (ite_one_zero_iff this).1 rfl
    rw [chi_zero_color, chi_zero_color, this]

theorem ind_zero_mem (c : Color k 0) : ind G H 0 c ∈ Vs G H 0 := by
  classical
  have h := mem_polySpan (gens0 G H) (ind G H 0 c) (fun x y hxy => by
    simp only [ind, chi_zero_eq_of x y hxy])
  have := polySpan_le_Vs _ 0 _ gens0_sub h
  simpa using this

/-! ### The step -/

variable (G H) in
/-- The neighbouring tuples `(v[q/1], …, v[q/k])` over all `q`. -/
noncomputable def nbr (x : Tup k G H) : Multiset (Fin k → Tup k G H) :=
  Sum.elim (fun p => (univ : Finset (Fin G.n)).val.map fun q i => .inl (Function.update p i q))
    (fun p => (univ : Finset (Fin H.n)).val.map fun q i => .inr (Function.update p i q)) x

lemma extOp_eq_nbr (f : Fin k → Tup k G H → ℚ) (x : Tup k G H) :
    extOp f x = ((nbr G H x).map fun y => ∏ j, f j (y j)).sum := by
  rcases x with p | p <;> simp [extOp, nbr, Multiset.map_map, Finset.sum_eq_multiset_sum] <;> rfl

lemma chi_succ (r : ℕ) (x : Tup k G H) :
    chi G H (r + 1) x = (chi G H r x, (nbr G H x).map fun y => chi G H r ∘ y) := by
  rcases x with p | p <;> simp [chi, color, nbr, Multiset.map_map] <;> rfl

open scoped Classical in
lemma extOp_ind (r : ℕ) (c : Fin k → Color k r) (x : Tup k G H) :
    extOp (fun j => ind G H r (c j)) x =
      (((nbr G H x).map fun y => chi G H r ∘ y).count c : ℚ) := by
  classical
  rw [extOp_eq_nbr]
  induction nbr G H x using Multiset.induction_on with
  | empty => simp
  | cons y s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.map_cons, Multiset.count_cons]
    have : ∏ j, ind G H r (c j) (y j) = if c = chi G H r ∘ y then 1 else 0 := by
      by_cases hc : c = chi G H r ∘ y
      · subst hc
        simp [ind]
      · rw [if_neg hc]
        obtain ⟨j, hj⟩ : ∃ j, chi G H r (y j) ≠ c j := by
          by_contra hcon
          push Not at hcon
          exact hc (funext fun j => (hcon j).symm)
        exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [ind, hj])
    rw [this]
    split_ifs <;> push_cast <;> ring

variable (G H) in
open scoped Classical in
/-- The generators for the step: the round-`r` class indicators and the extensions `N_c`. -/
noncomputable def gensSucc (r : ℕ) : Finset (Tup k G H → ℚ) :=
  (univ : Finset (Tup k G H)).image (fun x => ind G H r (chi G H r x)) ∪
    (univ : Finset (Fin k → Tup k G H)).image
      (fun y => extOp (fun j => ind G H r (chi G H r (y j))))

lemma chi_succ_eq_of (r : ℕ) (x y : Tup k G H) (h : ∀ g ∈ gensSucc G H r, g x = g y) :
    chi G H (r + 1) x = chi G H (r + 1) y := by
  classical
  rw [chi_succ, chi_succ]
  have h₁ : chi G H r x = chi G H r y := by
    by_contra hne
    have := h _ (by
      simp only [gensSucc, mem_union, mem_image, mem_univ, true_and]
      exact Or.inl ⟨x, rfl⟩)
    simp only [ind] at this
    rw [if_neg (Ne.symm hne)] at this
    simp at this
  refine Prod.ext h₁ (Multiset.ext.2 fun c => ?_)
  by_cases hc : ∃ z : Fin k → Tup k G H, chi G H r ∘ z = c
  · obtain ⟨z, rfl⟩ := hc
    have := h _ (by
      simp only [gensSucc, mem_union, mem_image, mem_univ, true_and]
      exact Or.inr ⟨z, rfl⟩)
    have e : (fun j => ind G H r (chi G H r (z j))) = fun j => ind G H r ((chi G H r ∘ z) j) :=
      rfl
    rw [e, extOp_ind, extOp_ind] at this
    exact_mod_cast this
  · push Not at hc
    rw [Multiset.count_eq_zero.2, Multiset.count_eq_zero.2]
    · intro hm
      obtain ⟨z, -, hz⟩ := Multiset.mem_map.1 hm
      exact hc z hz
    · intro hm
      obtain ⟨z, -, hz⟩ := Multiset.mem_map.1 hm
      exact hc z hz

theorem ind_succ_mem (hk : 1 ≤ k) (r : ℕ) (N : ℕ) (hr : ∀ c : Color k r, ind G H r c ∈ Vs G H N)
    (c : Color k (r + 1)) :
    ind G H (r + 1) c ∈ Vs G H ((Fintype.card (Tup k G H) - 1) * (1 + k * N)) := by
  classical
  have hsub : ((gensSucc G H r : Finset (Tup k G H → ℚ)) : Set _) ⊆
      (Vs (k := k) G H (1 + k * N) : Set (Tup k G H → ℚ)) := by
    intro g hg
    simp only [gensSucc, coe_union, coe_image, Set.mem_union, Set.mem_image, mem_coe] at hg
    rcases hg with ⟨x, -, rfl⟩ | ⟨z, -, rfl⟩
    · exact Vs_mono (by nlinarith) (hr _)
    · exact extOp_mem _ fun j => hr _
  have h := mem_polySpan (gensSucc G H r) (ind G H (r + 1) c) (fun x y hxy => by
    simp only [ind, chi_succ_eq_of r x y hxy])
  exact polySpan_le_Vs _ _ _ hsub h

theorem ind_mem (hk : 1 ≤ k) (r : ℕ) (c : Color k r) :
    ind G H r c ∈ Vs G H (nu k (Fintype.card (Tup k G H)) r) := by
  induction r with
  | zero => exact ind_zero_mem c
  | succ r ih => exact ind_succ_mem hk r _ ih c

end Lax119563Proofs.HomTensors

end HomTensors_Rounds

/-! ### Formerly `Lax119563Proofs.HomTensors.Unlabel` -/

section HomTensors_Unlabel

/-!
# From a good labeled graph to a colored graph

A good labeled graph `F` whose homomorphism counts into `G` and `H` differ yields a colored
graph `F'` of treewidth at most `k` with at most `k + N` vertices and `hom F' G ≠ hom F' H`:

* identify `eqv`-equivalent vertices (the quotient has at most `k + N` vertices, and the bag
  tree pushes forward to a tree decomposition of width `k`);
* a loop forbids all homomorphisms, so there is none; parallel edges and edge orientations are
  irrelevant;
* `hom(F, ·)` is the sum of `hom(F_κ, ·)` over the colorings `κ` (with colors of `G` and `H`)
  compatible with the color predicates, so one `F_κ` distinguishes `G` and `H`.
-/

namespace Lax119563Proofs.HomTensors

open Lax119563.ColoredGraphs Lax119563.ColoredHomomorphisms Lax228581.Treewidth Relation

variable {k : ℕ}

lemma card_eq_sum_fiber {α β : Type} [Finite α] [Fintype β] (P : α → Prop) (f : α → β) :
    Nat.card {a // P a} = ∑ b, Nat.card {a // P a ∧ f a = b} := by
  rw [← Nat.card_sigma]
  exact Nat.card_congr
    { toFun := fun a => ⟨f a.1, a.1, a.2, rfl⟩
      invFun := fun p => ⟨p.2.1, p.2.2.1⟩
      left_inv := fun a => rfl
      right_inv := by
        rintro ⟨b, a, h, rfl⟩
        rfl }

namespace LGraph

lemma IsHom.eqvGen {F : LGraph k} {G : ColoredGraph} {h : F.V → Fin G.n} (hh : F.IsHom G h)
    {a b : F.V} (hab : EqvGen F.eqv a b) : h a = h b := by
  induction hab with
  | rel x y hxy => exact hh.2.2 x y hxy
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- A good labeled graph distinguishing `G` and `H` by homomorphism counts yields a colored
graph of treewidth at most `k` with at most `k + N` vertices distinguishing them. -/
theorem exists_coloredGraph (F : LGraph k) {N : ℕ} (hF : F.Good N) (G H : ColoredGraph)
    (hne : F.homCount G ≠ F.homCount H) :
    ∃ F' : ColoredGraph, TreewidthAtMost F' k ∧ F'.n ≤ k + N ∧ hom F' G ≠ hom F' H := by
  classical
  obtain ⟨⟨D⟩, W, g, hW, hWc, hg⟩ := hF
  -- the quotient by `eqv`
  let Q := Quot F.eqv
  have : Finite Q := Finite.of_surjective (Quot.mk _) fun q => Quot.exists_rep q
  let n := Nat.card Q
  let e : Q ≃ Fin n := Finite.equivFin Q
  let π : F.V → Fin n := fun a => e (Quot.mk _ a)
  have hker : ∀ a b, π a = π b → EqvGen F.eqv a b := fun a b h =>
    Quot.eqvGen_exact (e.injective h)
  have hcompat' : ∀ a b, EqvGen F.eqv a b → π a = π b := fun a b h => by
    simp only [π, Quot.eqvGen_sound h]
  have hcompat : ∀ a b, F.eqv a b → π a = π b := fun a b h => hcompat' a b (EqvGen.rel _ _ h)
  have hsurj : Function.Surjective π := by
    intro x
    obtain ⟨a, ha⟩ := Quot.exists_rep (e.symm x)
    exact ⟨a, by simp [π, ha]⟩
  -- size
  have hn : n ≤ k + N := by
    have hs : Function.Surjective (Sum.elim (fun i => Quot.mk F.eqv (F.lab i))
        (fun w => Quot.mk F.eqv (g w))) := by
      intro q
      obtain ⟨a, rfl⟩ := Quot.exists_rep q
      rcases hg a with ⟨i, hi⟩ | ⟨w, hw⟩
      · exact ⟨.inl i, (Quot.eqvGen_sound hi).symm⟩
      · exact ⟨.inr w, (Quot.eqvGen_sound hw).symm⟩
    have := Nat.card_le_card_of_surjective _ hs
    have h3 : Nat.card (Quot F.eqv) ≤ k + Nat.card W := by simpa using this
    change Nat.card (Quot F.eqv) ≤ k + N
    omega
  -- loops forbid homomorphisms
  by_cases hloop : ∃ a b, F.adj a b ∧ π a = π b
  · exfalso
    obtain ⟨a, b, hab, hπ⟩ := hloop
    have hzero : ∀ G' : ColoredGraph, F.homCount G' = 0 := by
      intro G'
      rw [homCount, Nat.card_eq_zero]
      left
      refine ⟨fun ⟨h, hh⟩ => ?_⟩
      have h1 := hh.1 a b hab
      rw [hh.eqvGen (hker a b hπ)] at h1
      exact G'.graph.loopless.irrefl _ h1
    exact hne ((hzero G).trans (hzero H).symm)
  push Not at hloop
  -- the simple graph on the quotient
  let S : SimpleGraph (Fin n) := SimpleGraph.fromRel fun x y => ∃ a b, F.adj a b ∧ π a = x ∧ π b = y
  have htw : HasTreewidthAtMost S k := by
    refine D.T.hasTreewidthAtMost D.valid S π hsurj hker hcompat ?_ k D.width
    intro x y hxy
    rw [SimpleGraph.fromRel_adj] at hxy
    rcases hxy.2 with ⟨a, b, hab, rfl, rfl⟩ | ⟨a, b, hab, ha, hb⟩
    · exact ⟨a, b, rfl, rfl, Or.inl hab⟩
    · exact ⟨b, a, hb, ha, Or.inr hab⟩
  -- colorings
  let C := Finset.image G.color Finset.univ ∪ Finset.image H.color Finset.univ
  let Fκ : (Fin n → C) → ColoredGraph := fun κ => ⟨n, S, fun x => (κ x : ℕ)⟩
  let ok : (Fin n → C) → Prop := fun κ => ∀ a c, F.pred a c → (κ (π a) : ℕ) = c
  have hcount : ∀ G' : ColoredGraph, (∀ v, G'.color v ∈ C) →
      F.homCount G' = ∑ κ : Fin n → C, if ok κ then hom (Fκ κ) G' else 0 := by
    intro G' hC
    let πinv := Function.surjInv hsurj
    have hπinv : ∀ x, π (πinv x) = x := Function.surjInv_eq hsurj
    let Padj : (Fin n → Fin G'.n) → Prop := fun h' => ∀ x y, S.Adj x y → G'.graph.Adj (h' x) (h' y)
    let Ppred : (Fin n → Fin G'.n) → Prop :=
      fun h' => ∀ a c, F.pred a c → G'.color (h' (π a)) = c
    have hback : ∀ h, F.IsHom G' h → ∀ a, h (πinv (π a)) = h a := fun h hh a =>
      hh.eqvGen (hker _ _ (hπinv (π a)))
    -- (a) homomorphisms factor through the quotient
    have ha : F.homCount G' = Nat.card {h' : Fin n → Fin G'.n // Padj h' ∧ Ppred h'} := by
      refine Nat.card_congr
        { toFun := fun h => ⟨h.1 ∘ πinv, ?_, ?_⟩
          invFun := fun h' => ⟨h'.1 ∘ π, ?_, ?_, ?_⟩
          left_inv := ?_
          right_inv := ?_ }
      · intro x y hxy
        rw [SimpleGraph.fromRel_adj] at hxy
        rcases hxy.2 with ⟨a, b, hab, rfl, rfl⟩ | ⟨a, b, hab, rfl, rfl⟩
        · simp only [Function.comp_apply, hback h.1 h.2]
          exact h.2.1 a b hab
        · simp only [Function.comp_apply, hback h.1 h.2]
          exact (h.2.1 a b hab).symm
      · intro a c hac
        simp only [Function.comp_apply, hback h.1 h.2]
        exact h.2.2.1 a c hac
      · intro a b hab
        exact h'.2.1 _ _ ((SimpleGraph.fromRel_adj _ _ _).2
          ⟨hloop a b hab, Or.inl ⟨a, b, hab, rfl, rfl⟩⟩)
      · exact h'.2.2
      · intro a b hab
        simp only [Function.comp_apply, hcompat a b hab]
      · intro h
        apply Subtype.ext
        funext a
        exact hback h.1 h.2 a
      · intro h'
        apply Subtype.ext
        funext x
        simp only [Function.comp_apply, hπinv]
    -- (b) split by the coloring
    let col : (Fin n → Fin G'.n) → (Fin n → C) := fun h' x => ⟨G'.color (h' x), hC _⟩
    rw [ha, card_eq_sum_fiber _ col]
    refine Finset.sum_congr rfl fun κ _ => ?_
    have hcol : ∀ h', col h' = κ ↔ ∀ x, G'.color (h' x) = κ x := by
      intro h'
      simp only [col, funext_iff, Subtype.ext_iff]
    split_ifs with hok
    · -- (c), (d)
      refine Nat.card_congr
        { toFun := fun h => ⟨⟨h.1, fun hxy => h.2.1.1 _ _ hxy⟩, (hcol h.1).1 h.2.2⟩
          invFun := fun h => ⟨⇑h.1, ⟨fun x y hxy => h.1.map_rel hxy, ?_⟩, (hcol ⇑h.1).2 h.2⟩
          left_inv := fun h => rfl
          right_inv := fun h => rfl }
      intro a c hac
      rw [h.2 (π a)]
      exact hok a c hac
    · rw [Nat.card_eq_zero]
      left
      refine ⟨fun h => ?_⟩
      obtain ⟨h', ⟨-, hp⟩, hκ⟩ := h
      refine hok fun a c hac => ?_
      rw [← (hcol h').1 hκ (π a)]
      exact hp a c hac
  have hCG : ∀ v, G.color v ∈ C := fun v => by simp [C]
  have hCH : ∀ v, H.color v ∈ C := fun v => by simp [C]
  rw [hcount G hCG, hcount H hCH] at hne
  by_contra hall
  push Not at hall
  refine hne (Finset.sum_congr rfl fun κ _ => ?_)
  split_ifs
  · exact hall (Fκ κ) htw hn
  · rfl

end LGraph

end Lax119563Proofs.HomTensors

end HomTensors_Unlabel
