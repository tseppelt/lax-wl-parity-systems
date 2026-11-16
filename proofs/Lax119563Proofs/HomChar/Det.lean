import Mathlib
import Lax119563.WeisfeilerLeman

/-!
# Tensors determined by Weisfeiler–Leman colors

A *tensor family* assigns to every colored graph `G` a function `(Fin k → Fin G.n) → ℕ`. It is
*determined in round `r`* (`Det r φ`) if its value at `p̄` is a function of the round-`r` color
`χ^{(r)}_k[G](p̄)`, uniformly in `G` (colors are compared syntactically across graphs).

Determined families contain the atomic tensors (round `0`), are closed under products, and under
the *extension* `p̄ ↦ ∑_q ∏_i ψ_i(p̄[q/i])` (one more round). If `k`-WL does not distinguish `G`
and `H` after `r` rounds, then the sums over all tuples of a round-`r` determined family agree.
-/

namespace Lax119563Proofs.HomChar

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman

variable {k : ℕ}

/-- A tensor family: a function on the `k`-tuples of every colored graph. -/
abbrev Fam (k : ℕ) := (G : ColoredGraph) → (Fin k → Fin G.n) → ℕ

/-- `φ` is determined by the round-`r` colors of `k`-WL. -/
def Det (r : ℕ) (φ : Fam k) : Prop :=
  ∃ f : Color k r → ℕ, ∀ G p, φ G p = f (color G r p)

/-- `φ` is determined by the colors of some round. -/
def DetAny (φ : Fam k) : Prop := ∃ r, Det r φ

lemma Det.succ {r : ℕ} {φ : Fam k} (h : Det r φ) : Det (r + 1) φ := by
  obtain ⟨f, hf⟩ := h
  exact ⟨fun c => f c.1, fun G p => hf G p⟩

lemma Det.mono {r s : ℕ} {φ : Fam k} (h : Det r φ) (hrs : r ≤ s) : Det s φ := by
  induction s, hrs using Nat.le_induction with
  | base => exact h
  | succ s _ ih => exact ih.succ

lemma det_atp (F : AtomicType k → ℕ) : Det 0 (k := k) (fun G p => F (atp G p)) :=
  ⟨F, fun _ _ => rfl⟩

lemma det_const (a : ℕ) : Det 0 (k := k) (fun _ _ => a) := ⟨fun _ => a, fun _ _ => rfl⟩

lemma Det.mul {r : ℕ} {φ ψ : Fam k} (h1 : Det r φ) (h2 : Det r ψ) :
    Det r (fun G p => φ G p * ψ G p) := by
  obtain ⟨f, hf⟩ := h1
  obtain ⟨g, hg⟩ := h2
  exact ⟨fun c => f c * g c, fun G p => by simp only [hf, hg]⟩

lemma DetAny.mul {φ ψ : Fam k} (h1 : DetAny φ) (h2 : DetAny ψ) :
    DetAny (fun G p => φ G p * ψ G p) := by
  obtain ⟨r, h1⟩ := h1
  obtain ⟨s, h2⟩ := h2
  exact ⟨max r s, (h1.mono (le_max_left _ _)).mul (h2.mono (le_max_right _ _))⟩

lemma Det.congr {r : ℕ} {φ ψ : Fam k} (h : Det r φ) (e : ∀ G p, ψ G p = φ G p) : Det r ψ := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun G p => (e G p).trans (hf G p)⟩

lemma DetAny.prod {ι : Type*} (s : Finset ι) {φ : ι → Fam k} (h : ∀ j ∈ s, DetAny (φ j)) :
    DetAny (fun G p => ∏ j ∈ s, φ j G p) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact ⟨0, det_const 1⟩
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- The extension `p̄ ↦ ∑_q ∏_i ψ_i(p̄[q/i])` of round-`r` determined families is determined in
round `r + 1`. -/
lemma det_ext {r : ℕ} {ψ : Fin k → Fam k} (h : ∀ i, Det r (ψ i)) :
    Det (r + 1) (fun G p => ∑ x, ∏ i, ψ i G (Function.update p i x)) := by
  choose f hf using h
  refine ⟨fun c => (c.2.map fun v => ∏ i, f i (v i)).sum, fun G p => ?_⟩
  simp only [color, Multiset.map_map, Function.comp_def]
  rw [Finset.sum_eq_multiset_sum]
  congr 1
  refine Multiset.map_congr rfl fun x _ => ?_
  exact Finset.prod_congr rfl fun i _ => hf i G _

/-! ### Extension-ready families

`Ext r Φ`: `Φ G p̄ x = χ(p̄) · ∏_i ψ_i(p̄[x/i])` with round-`r` determined `χ, ψ_i`. Summing over
`x` gives a family determined in round `r + 1`. -/

/-- A function of a tuple `p̄` and a vertex `x`. -/
abbrev Fam1 (k : ℕ) := (G : ColoredGraph) → (Fin k → Fin G.n) → Fin G.n → ℕ

/-- `Φ G p̄ x = χ(p̄) · ∏_i ψ_i(p̄[x/i])` for round-`r` determined `χ` and `ψ_i`. -/
def Ext (r : ℕ) (Φ : Fam1 k) : Prop :=
  ∃ (χ : Fam k) (ψ : Fin k → Fam k), Det r χ ∧ (∀ i, Det r (ψ i)) ∧
    ∀ G p x, Φ G p x = χ G p * ∏ i, ψ i G (Function.update p i x)

/-- `Ext r Φ` for some `r`. -/
def ExtAny (Φ : Fam1 k) : Prop := ∃ r, Ext r Φ

lemma Ext.mono {r s : ℕ} {Φ : Fam1 k} (h : Ext r Φ) (hrs : r ≤ s) : Ext s Φ := by
  obtain ⟨χ, ψ, h1, h2, h3⟩ := h
  exact ⟨χ, ψ, h1.mono hrs, fun i => (h2 i).mono hrs, h3⟩

lemma Ext.mul {r : ℕ} {Φ Ψ : Fam1 k} (h1 : Ext r Φ) (h2 : Ext r Ψ) :
    Ext r (fun G p x => Φ G p x * Ψ G p x) := by
  obtain ⟨χ, ψ, a1, a2, a3⟩ := h1
  obtain ⟨χ', ψ', b1, b2, b3⟩ := h2
  refine ⟨fun G p => χ G p * χ' G p, fun i G p => ψ i G p * ψ' i G p, a1.mul b1,
    fun i => (a2 i).mul (b2 i), fun G p x => ?_⟩
  simp only [a3, b3, Finset.prod_mul_distrib]
  ring

lemma ExtAny.congr {Φ Ψ : Fam1 k} (h : ExtAny Φ) (e : ∀ G p x, Ψ G p x = Φ G p x) :
    ExtAny Ψ := by
  obtain ⟨r, χ, ψ, h1, h2, h3⟩ := h
  exact ⟨r, χ, ψ, h1, h2, fun G p x => (e G p x).trans (h3 G p x)⟩

lemma ExtAny.mul {Φ Ψ : Fam1 k} (h1 : ExtAny Φ) (h2 : ExtAny Ψ) :
    ExtAny (fun G p x => Φ G p x * Ψ G p x) := by
  obtain ⟨r, h1⟩ := h1
  obtain ⟨s, h2⟩ := h2
  exact ⟨max r s, (h1.mono (le_max_left _ _)).mul (h2.mono (le_max_right _ _))⟩

lemma extAny_const (a : ℕ) : ExtAny (k := k) (fun _ _ _ => a) := by
  refine ⟨0, fun _ _ => a, fun _ _ _ => 1, det_const a, fun _ => det_const 1, ?_⟩
  intro G p x
  simp

lemma ExtAny.prod {ι : Type*} (s : Finset ι) {Φ : ι → Fam1 k} (h : ∀ j ∈ s, ExtAny (Φ j)) :
    ExtAny (fun G p x => ∏ j ∈ s, Φ j G p x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using extAny_const 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma extAny_left {φ : Fam k} (h : DetAny φ) : ExtAny (fun G p (_ : Fin G.n) => φ G p) := by
  obtain ⟨r, h⟩ := h
  exact ⟨r, φ, fun _ _ _ => 1, h, fun _ => (det_const 1).mono (Nat.zero_le _),
    fun G p x => by simp⟩

lemma extAny_at {φ : Fam k} (h : DetAny φ) (i : Fin k) :
    ExtAny (fun G p x => φ G (Function.update p i x)) := by
  classical
  obtain ⟨r, h⟩ := h
  refine ⟨r, fun _ _ => 1, fun j G p => if j = i then φ G p else 1,
    (det_const 1).mono (Nat.zero_le _), fun j => ?_, fun G p x => ?_⟩
  · by_cases hj : j = i
    · simpa [hj] using h
    · simpa [hj] using (det_const 1).mono (Nat.zero_le r)
  · simp [Finset.prod_ite_eq']

lemma ExtAny.sum {Φ : Fam1 k} (h : ExtAny Φ) : DetAny (fun G p => ∑ x, Φ G p x) := by
  obtain ⟨r, χ, ψ, h1, h2, h3⟩ := h
  refine ⟨r + 1, ?_⟩
  have := (h1.succ).mul (det_ext h2)
  obtain ⟨f, hf⟩ := this
  refine ⟨f, fun G p => ?_⟩
  rw [← hf]
  simp only [h3, Finset.mul_sum]

/-! ### Equal histograms -/

lemma sum_eq_of_det {r : ℕ} {φ : Fam k} (h : Det r φ) {G H : ColoredGraph}
    (hGH : ¬ DistinguishesAfter k r G H) : ∑ p, φ G p = ∑ q, φ H q := by
  classical
  obtain ⟨f, hf⟩ := h
  simp only [hf]
  have hm : (Finset.univ : Finset (Fin k → Fin G.n)).val.map (color G r) =
      (Finset.univ : Finset (Fin k → Fin H.n)).val.map (color H r) := by
    ext c
    simp only [DistinguishesAfter, not_exists, not_not] at hGH
    have := hGH c
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
      Fintype.card_subtype] at this
    rw [Multiset.count_map, Multiset.count_map, ← Finset.filter_val, ← Finset.filter_val,
      ← Finset.card_def, ← Finset.card_def]
    convert this using 2 <;> ext <;> simp [eq_comm]
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum, ← Function.comp_def f,
    ← Multiset.map_map, hm, Multiset.map_map]
  rfl

end Lax119563Proofs.HomChar
