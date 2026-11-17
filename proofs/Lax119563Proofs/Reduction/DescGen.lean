import Lax119563Proofs.Reduction.EdgeUpd

/-!
# The description of one output graph

* `edgePass M s ε b`: the hub edge passes; **`out_edgePass`**: it emits the flattened edge list
  of `outGraph (Iv …) ε`;
* `descGen M s ε b`: `nOut`, the colours, the edge count (half the length of a counting run of
  the edge pass) and the edges; **`out_descGen`**: it emits `graphDescription (outGraph …)`.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs Lax119563Proofs.Matrix
open Lax119563.ColoredGraphs Lax119563.BinaryEncodings

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

namespace Gn

/-- The hub edge passes. -/
def edgePass (M : Machine) (s ε b : ℕ) : Gn :=
  seqL [edgeUpd M s ε b, edgeJunc M s ε b, edgeLink M s ε b]

/-- The description of the output graph `G'_ε` (globals below depth `b`). -/
def descGen (M : Machine) (s ε b : ℕ) : Gn :=
  seqL [.emit gnOut, colPass M s b,
    .count (edgePass M s ε (b + 1)) (.seq (.emit (half (var b))) (edgePass M s ε (b + 1)))]

end Gn

theorem out_edgePass {ρ : List ℕ} {b ε : ℕ} (hρ : ρ.length = b) (hG : GlobOK M x s ℓ H ρ)
    (hℓ : 0 < ℓ) (hs : 1 ≤ s) (hε : ε ≤ 1) :
    (Gn.edgePass M s ε b).out x ρ =
      (edgeList (outGraph (Iv M x s ℓ H) (ε : ZMod 2))).flatMap (fun e => [e.1, e.2]) := by
  rw [edges_flat, Gn.edgePass, Gn.out_seqL]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [out_edgeUpd hρ hG hℓ hs hε, out_edgeJunc hρ hG hℓ hs hε, out_edgeLink hρ hG hℓ hs hε,
    List.append_assoc]

lemma length_flatMap_pair (l : List (ℕ × ℕ)) :
    (l.flatMap fun e => [e.1, e.2]).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]; ring

lemma map_finRange_val {β : Type} (n : ℕ) (f : ℕ → β) :
    (List.finRange n).map (fun z : Fin n => f z) = (List.range n).map f := by
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  rfl

/-- **The description of one output graph.** -/
theorem out_descGen {ρ : List ℕ} {b ε : ℕ} (hρ : ρ.length = b) (hG : GlobOK M x s ℓ H ρ)
    (hℓ : 0 < ℓ) (hs : 1 ≤ s) (hε : ε ≤ 1) :
    (Gn.descGen M s ε b).out x ρ = graphDescription (outGraph (Iv M x s ℓ H) (ε : ZMod 2)) := by
  have hρ1 : (ρ ++ [0]).length = b + 1 := by simp [hρ]
  have hE0 := out_edgePass hρ1 (hG.append [0]) hℓ hs hε
  simp only [Gn.descGen, Gn.out_seqL, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Gn.out, hG.enOut, out_colPass hρ hG hℓ hs, hE0, length_flatMap_pair]
  set m := (edgeList (outGraph (Iv M x s ℓ H) (ε : ZMod 2))).length
  have hρ2 : (ρ ++ [2 * m]).length = b + 1 := by simp [hρ]
  rw [out_edgePass hρ2 (hG.append _) hℓ hs hε]
  have hhalf : (half (var b)).eval (ρ ++ [2 * m]) = m := by
    rw [Xp.eval_half', eval_var, ← hρ, show ρ.length = ρ.length + 0 from rfl, getD_app]
    simp
  rw [hhalf, graphDescription]
  have hc : (List.finRange (outGraph (Iv M x s ℓ H) (ε : ZMod 2)).n).map
      (outGraph (Iv M x s ℓ H) (ε : ZMod 2)).color =
      (List.range (nOut (Iv M x s ℓ H))).map (outColor (Iv M x s ℓ H)) :=
    map_finRange_val (nOut (Iv M x s ℓ H)) (outColor (Iv M x s ℓ H))
  have hn : (outGraph (Iv M x s ℓ H) (ε : ZMod 2)).n = nOut (Iv M x s ℓ H) := rfl
  rw [hc, hn]
  simp [m]

end Lax119563Proofs.Reduction
