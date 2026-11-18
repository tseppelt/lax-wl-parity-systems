import Lax119563Proofs.Compiler.Final
import Lax119563Proofs.Reduction.CostMachine

/-!
# The length of the output

With `n = |ordL I|` vertices per graph: every entry of `gDesc I ε` is at most `3 n`
(`gDesc_le`), `gDesc I ε` has at most `2 + 7 n` entries (`length_gDesc_le`), hence
`|encodeNats (gDesc I 0 ++ gDesc I 1)| ≤ 2 (2 + 7 n) (2 w + 1)` whenever `3 n < 2 ^ w`
(`length_out_le`), and `n ≤ 16 S` for `k ≥ 2` (`length_ordL_le`).
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs
open Lax119563.BinaryEncodings Lax119563Proofs.Matrix Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

lemma lt_of_mem_colorsOf : ∀ (s : ℕ) (ns : List ℕ) (c : ℕ), c ∈ colorsOf s ns → c < s + ns.sum
  | _, [], c, h => by simp [colorsOf] at h
  | s, n :: ns, c, h => by
    simp only [colorsOf, List.mem_append, List.mem_replicate] at h
    rcases h with ⟨hn, rfl⟩ | h
    · simp; omega
    · have := lt_of_mem_colorsOf (s + n) ns c h
      simp; omega

lemma length_colorsOf : ∀ (s : ℕ) (ns : List ℕ), (colorsOf s ns).length = ns.sum
  | _, [] => rfl
  | s, n :: ns => by simp [colorsOf, length_colorsOf (s + n) ns]

lemma edgeList_lt (G : ColoredGraph) {e : ℕ × ℕ} (he : e ∈ edgeList G) :
    e.1 < G.n ∧ e.2 < G.n := by
  classical
  unfold edgeList at he
  simp only [List.mem_flatMap, List.mem_map] at he
  obtain ⟨u, -, v, hv, rfl⟩ := he
  refine ⟨u.2, ?_⟩
  change v ∈ List.flatMap (fun a : Fin G.n => [(a : ℕ)]) _ at hv
  simp only [List.mem_flatMap, List.mem_singleton] at hv
  obtain ⟨a, -, rfl⟩ := hv
  exact a.2

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) (ε : ZMod 2)

lemma length_slotsOf (X : ICls I) (l : Lab) : (slotsOf I X l).length ≤ 3 := by
  cases X <;> simp [slotsOf]

lemma length_nbrPos (x : VName I) : (nbrPos I ε x).length ≤ 3 := by
  unfold nbrPos
  rw [List.length_mergeSort]
  exact (List.length_filterMap_le _ _).trans (length_slotsOf I _ _)

lemma length_gEdges : (gEdges I ε).length ≤ 3 * (ordL I).length := by
  rw [← edgeList_eq_gEdges, edgeList_nbrPos, List.length_flatMap]
  calc ((List.finRange (ordL I).length).map fun u : Fin (ordL I).length =>
          ((nbrPos I ε (ordL I)[(u : ℕ)]).map fun v => ((u : ℕ), v)).length).sum
      ≤ ((List.finRange (ordL I).length).map fun _ => 3).sum := by
        apply List.sum_le_sum
        intro u _
        simpa using length_nbrPos I ε _
    _ = 3 * (ordL I).length := by simp [Nat.mul_comm]

lemma mem_gEdges_lt {e : ℕ × ℕ} (he : e ∈ gEdges I ε) :
    e.1 < (ordL I).length ∧ e.2 < (ordL I).length := by
  rw [← edgeList_eq_gEdges] at he
  exact edgeList_lt _ he

/-- Every entry of `gDesc I ε` is at most `3 n`. -/
lemma gDesc_le {v : ℕ} (hv : v ∈ gDesc I ε) : v ≤ 3 * (ordL I).length := by
  have hn := length_ordL I
  have hm := length_gEdges I ε
  simp only [gDesc, List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap] at hv
  rcases hv with rfl | h | rfl | ⟨e, he, hv⟩
  · omega
  · have := lt_of_mem_colorsOf 0 _ _ h; omega
  · exact hm
  · have := mem_gEdges_lt I ε he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> omega

lemma length_gDesc_le : (gDesc I ε).length ≤ 2 + 7 * (ordL I).length := by
  have hn := length_ordL I
  have hm := length_gEdges I ε
  have e2 : ((gEdges I ε).flatMap fun e => [e.1, e.2]).length = 2 * (gEdges I ε).length := by
    rw [List.length_flatMap]; simp [Nat.mul_comm]
  simp only [gDesc, List.cons_append, List.length_cons, List.length_append, length_colorsOf, e2]
  omega

/-- **The length of the output.** -/
theorem length_out_le {w : ℕ} (hw : 3 * (ordL I).length < 2 ^ w) :
    (encodeNats (gDesc I 0 ++ gDesc I 1)).length ≤
      2 * (2 + 7 * (ordL I).length) * (2 * w + 1) := by
  have h := length_encodeNats_le (l := gDesc I 0 ++ gDesc I 1) (w := w) fun v hv => by
    rcases List.mem_append.mp hv with h | h
    · exact lt_of_le_of_lt (gDesc_le I 0 h) hw
    · exact lt_of_le_of_lt (gDesc_le I 1 h) hw
  have h0 := length_gDesc_le I 0
  have h1 := length_gDesc_le I 1
  rw [List.length_append] at h
  calc _ ≤ _ := h
    _ ≤ (2 * (2 + 7 * (ordL I).length)) * (2 * w + 1) :=
      Nat.mul_le_mul_right _ (by omega)

lemma length_ordL_le (hk : 2 ≤ k) : (ordL I).length ≤ 16 * sizeParameter I := by
  rw [(ordL_perm I).length_eq]; exact card_vertexList_le hk

end Lax119563Proofs.Compiler
