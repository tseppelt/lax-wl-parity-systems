import Mathlib
import Lax119563Proofs.Reduction.OutEdges
import Lax119563.BinaryEncodings

/-!
# The edge list of the output graphs

Hubs are numbered below all non-hubs, and the neighbor candidates of a hub are listed in
increasing order of their numbers, provided that ternary schemas satisfy `locU < locV`
(`TernOrdered`). So the edge list of `outGraph I ε` is, for every number `u` in increasing
order, the pairs `(u, v)` for `v` in `upNbrs I ε u`, where `upNbrs` of the number of a valid
hub `a` is `(hubNbrs I ε a).map (num I)`, and empty for all other numbers.
-/

open Lax119563.ColoredGraphs Lax119563.BinaryEncodings Lax119563.ImplicitParitySystems
open Lax119563.MatrixCompiler Lax119563Proofs.Matrix

namespace Lax119563Proofs.Reduction

variable {s ℓ : ℕ} (I : ImplicitParitySystem (s + 1) ℓ)

/-- Ternary schemas list their first two locations in increasing order. -/
def TernOrdered : Prop :=
  ∀ e : Fin I.schemas.length, isTern (sch I e) = true → locU (sch I e) < locV (sch I e)

lemma num_lt_num_of_famNum_lt {X Y : ICls I} (l m : Lab) (h : famNum I X < famNum I Y) :
    num I (X, l) < num I (Y, m) := by
  unfold num classNum
  simp only
  have := labNum_lt l
  have r1 := regVal_lt (coordOf I X).2
  have i1 := (coordOf I X).1.isLt
  have hA : (coordOf I X).1.val + (s + 1) * famNum I X + 1 ≤
      (coordOf I Y).1.val + (s + 1) * famNum I Y := by nlinarith
  have hB : ((coordOf I X).1.val + (s + 1) * famNum I X + 1) * 2 ^ ℓ ≤
      ((coordOf I Y).1.val + (s + 1) * famNum I Y) * 2 ^ ℓ := Nat.mul_le_mul_right _ hA
  nlinarith

/-- Every coordinate has a nonzero entry in some step (`k ≥ 2`). -/
lemma prevStep_numSteps_ne_none (hs : 1 ≤ s) (c : Coord (s + 1) ℓ) :
    prevStep c (numSteps (s + 1) ℓ) ≠ none := by
  intro h
  have hz := prevStep_none h
  set j : ℕ := if c.1.val < s then c.1.val else 0 with hj
  have hjs : j < s := by rw [hj]; split_ifs <;> omega
  have hjN : j < numSteps (s + 1) ℓ := by
    unfold numSteps
    have h1 : s ≤ s + 1 - 1 + ℓ := by omega
    have h2 : s + 1 - 1 + ℓ ≤ (s + 1 + 1) * (s + 1 - 1 + ℓ) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have := hz j hjN
  have hM : 0 < s + 1 - 1 + ℓ := by omega
  unfold ent at this
  rw [dif_pos hM] at this
  have hrow : stepRow hM j = .inl ⟨j, by omega⟩ := by
    unfold stepRow
    have e : (⟨j % (s + 1 - 1 + ℓ), Nat.mod_lt _ hM⟩ : Fin (s + 1 - 1 + ℓ)) =
        Fin.castAdd ℓ (⟨j, by omega⟩ : Fin (s + 1 - 1)) :=
      Fin.ext (by simp; exact Nat.mod_eq_of_lt (by omega))
    rw [e, finSumFinEquiv_symm_apply_castAdd]
  rw [hrow] at this
  simp only [checkMatrix, Matrix.of_apply] at this
  rw [if_pos (by rw [hj]; split_ifs with h' <;> [left; right] <;> omega)] at this
  exact one_ne_zero this


lemma famNum_nonhub_ge {Y : ICls I} (h : isHub I Y = false) :
    I.schemas.length * numSteps (s + 1) ℓ + 2 * I.schemas.length ≤ famNum I Y := by
  cases Y <;> simp only [isHub, Bool.true_eq_false] at h <;> simp only [famNum] <;> omega

lemma famNum_hub_lt {X : ICls I} (hX : ClsValid I X) (h : isHub I X = true) :
    famNum I X < I.schemas.length * numSteps (s + 1) ℓ + 2 * I.schemas.length := by
  cases X with
  | upd e σ c =>
    have := e.isLt
    have hσ := hX.1
    simp only [famNum]
    have : (e.val + 1) * numSteps (s + 1) ℓ ≤ I.schemas.length * numSteps (s + 1) ℓ :=
      Nat.mul_le_mul_right _ this
    nlinarith
  | junc e c => have := e.isLt; simp only [famNum]; omega
  | link e c => have := e.isLt; simp only [famNum]; omega
  | _ => simp [isHub] at h

lemma numSteps_pos (hs : 1 ≤ s) : 0 < numSteps (s + 1) ℓ := by
  unfold numSteps; apply Nat.mul_pos <;> omega

lemma famNum_trackAt_lt (e : Fin I.schemas.length) (c : Coord (s + 1) ℓ) (σ : ℕ) :
    famNum I (trackAt I e c σ) < famNum I (.track e σ c) := by
  have he := e.isLt
  rcases trackAt_cases e c σ with h | ⟨σ', hσ', h⟩ <;> rw [h]
  · rcases startCls_cases e c with h' | h' <;> rw [h'] <;> simp only [famNum]
    · omega
    · have := (locU (sch I e)).isLt; omega
  · simp only [famNum]; omega

lemma famNum_track_lt_coef (hs : 1 ≤ s) (e : Fin I.schemas.length) (c : Coord (s + 1) ℓ)
    (σ : ℕ) : famNum I (.track e σ c) < famNum I (.coef e σ) := by
  have he := e.isLt
  have := numSteps_pos (ℓ := ℓ) hs
  have : 0 < I.schemas.length * numSteps (s + 1) ℓ := Nat.mul_pos (by omega) this
  simp only [famNum]; omega

lemma nbrCand_sorted (hs : 1 ≤ s) (hT : TernOrdered I) {X : ICls I} (hX : ClsValid I X)
    (l : Lab) : (nbrCand I X l).Pairwise (fun p q => famNum I p.1 < famNum I q.1) := by
  cases X with
  | upd e σ c =>
    have h1 := famNum_trackAt_lt I e c σ
    have h2 := famNum_track_lt_coef I hs e c σ
    simp only [nbrCand, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
      implies_true]
    omega
  | junc e c =>
    have hlt := hT e hX.1
    have hV := (locV (sch I e)).isLt
    have he := e.isLt
    simp only [nbrCand, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
      implies_true, famNum]
    rw [Fin.lt_def] at hlt
    omega
  | link e c =>
    have he := e.isLt
    have hne := prevStep_numSteps_ne_none hs c
    obtain ⟨σ', hσ'⟩ := Option.ne_none_iff_exists'.mp hne
    have ht : trackAt I e c (numSteps (s + 1) ℓ) = .track e σ' c := by simp [trackAt, hσ']
    simp only [nbrCand, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
      implies_true, ht, endCls, famNum]
    have := (locEnd (sch I e)).isLt
    omega
  | _ => simp [nbrCand]

lemma hubNbrs_sorted (hs : 1 ≤ s) (hT : TernOrdered I) (ε : ZMod 2) {a : VName I}
    (ha : Valid I a) : ((hubNbrs I ε a).map (num I)).Pairwise (· < ·) := by
  unfold hubNbrs
  rw [List.pairwise_map]
  apply List.Pairwise.filter
  rw [List.pairwise_map]
  exact (nbrCand_sorted I hs hT ha.1 a.2).imp fun h => num_lt_num_of_famNum_lt I _ _ h

lemma valid_of_mem_hubNbrs {ε : ZMod 2} {a b : VName I} (h : b ∈ hubNbrs I ε a) :
    Valid I b := by
  unfold hubNbrs at h
  simpa using (List.mem_filter.mp h).2

lemma num_lt_of_mem_hubNbrs {ε : ZMod 2} {a b : VName I} (ha : Valid I a)
    (h : b ∈ hubNbrs I ε a) : num I a < num I b := by
  obtain ⟨h1, h2⟩ := mem_hubNbrs_nonhub I h
  have := famNum_hub_lt I ha.1 h1
  have := famNum_nonhub_ge I h2
  exact num_lt_num_of_famNum_lt I _ _ (by omega)

/-! ## The edge list -/

open Classical in
/-- The neighbors of `u` with larger numbers, in increasing order. -/
noncomputable def upNbrs (ε : ZMod 2) (u : ℕ) : List ℕ :=
  (List.range (nOut I)).filter fun v => u < v ∧ outAdj I ε u v

lemma mem_upNbrs {ε : ZMod 2} {u v : ℕ} :
    v ∈ upNbrs I ε u ↔ v < nOut I ∧ u < v ∧ outAdj I ε u v := by
  simp [upNbrs]

lemma upNbrs_sorted (ε : ZMod 2) (u : ℕ) : (upNbrs I ε u).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

lemma eq_of_pairwise_lt {l₁ l₂ : List ℕ} (h₁ : l₁.Pairwise (· < ·)) (h₂ : l₂.Pairwise (· < ·))
    (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁ = l₂ := by
  have n₁ : l₁.Nodup := h₁.imp ne_of_lt
  have n₂ : l₂.Nodup := h₂.imp ne_of_lt
  exact ((List.perm_ext_iff_of_nodup n₁ n₂).mpr h).eq_of_pairwise
    (fun _ _ _ _ h1 h2 => absurd (h1.trans h2) (lt_irrefl _)) h₁ h₂

lemma upNbrs_hub (hs : 1 ≤ s) (hT : TernOrdered I) (ε : ZMod 2) {a : VName I}
    (ha : Valid I a) (hh : isHub I a.1 = true) :
    upNbrs I ε (num I a) = (hubNbrs I ε a).map (num I) := by
  refine eq_of_pairwise_lt (upNbrs_sorted I ε _) (hubNbrs_sorted I hs hT ε ha) fun v => ?_
  rw [mem_upNbrs, List.mem_map]
  constructor
  · rintro ⟨-, -, a', b, ha', hb, h1, rfl, h⟩
    rw [num_injective I ha' ha h1] at h
    exact ⟨b, (adjN_hub_iff I ε hh hb).mp h, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    have hbv := valid_of_mem_hubNbrs I hb
    exact ⟨num_lt I hbv, num_lt_of_mem_hubNbrs I ha hb, a, b, ha, hbv, rfl, rfl,
      (adjN_hub_iff I ε hh hbv).mpr hb⟩

lemma upNbrs_nonhub (ε : ZMod 2) {a : VName I} (ha : Valid I a)
    (hh : isHub I a.1 = false) : upNbrs I ε (num I a) = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro v hv
  rw [mem_upNbrs] at hv
  obtain ⟨-, hlt, a', b, ha', hb, h1, rfl, h⟩ := hv
  rw [num_injective I ha' ha h1] at h
  rcases (adjN_iff_hubNbrs I ε ha hb).mp h with ⟨h', -⟩ | ⟨-, h'⟩
  · rw [hh] at h'; cases h'
  · have := num_lt_of_mem_hubNbrs I hb h'
    omega

lemma upNbrs_invalid (ε : ZMod 2) {u : ℕ} (hu : ¬ OutValid I u) : upNbrs I ε u = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro v hv
  exact hu (outAdj_valid I ((mem_upNbrs I).mp hv).2.2)

lemma flatMap_finRange {β : Type} (n : ℕ) (f : ℕ → List β) :
    (List.finRange n).flatMap (fun u => f u.val) = (List.range n).flatMap f := by
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]

lemma filter_finRange_map (n : ℕ) (p : ℕ → Bool) :
    ((List.finRange n).filter (fun v => p v.val)).map Fin.val = (List.range n).filter p := by
  rw [← List.map_coe_finRange_eq_range, List.filter_map]
  rfl

lemma flatMap_singleton_eq_map {α β : Type} (f : α → β) (l : List α) :
    l.flatMap (fun a => [f a]) = l.map f := by
  induction l <;> simp_all

/-- **The edge list of the output graphs.** -/
theorem edgeList_outGraph (ε : ZMod 2) :
    edgeList (outGraph I ε) =
      (List.range (nOut I)).flatMap fun u => (upNbrs I ε u).map fun v => (u, v) := by
  classical
  unfold edgeList
  rw [← flatMap_finRange]
  congr 1
  funext u
  rw [upNbrs, ← filter_finRange_map, List.map_map]
  have : (List.finRange (outGraph I ε).n).filter
      (fun v => decide (u < v ∧ (outGraph I ε).graph.Adj u v)) =
      (List.finRange (nOut I)).filter
        (fun v => decide ((u : ℕ) < v.val ∧ outAdj I ε u v.val)) := by
    apply List.filter_congr
    intro v _
    rw [decide_eq_decide]
    exact Iff.rfl
  rw [this]
  generalize List.filter _ (List.finRange (nOut I)) = L
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.map_cons, Function.comp_apply] at ih ⊢
    rw [← ih]
    rfl

end Lax119563Proofs.Reduction
