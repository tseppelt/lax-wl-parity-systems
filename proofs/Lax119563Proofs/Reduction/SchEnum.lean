import Lax119563Proofs.Reduction.CmdEnum
import Lax119563Proofs.Reduction.CountIdx

/-!
# Towards the schema enumerator

`keys_pairwise`: the keys `(location number, move index)` of the records produced by the
command enumerator strictly increase (lexicographically), so the index of a command in the
code-ordered command list is the number of records with a smaller key (`CountIdx`), which a
generator computes with `Gn.count` over a nested `cmdEnum`.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp

variable {M : Machine} {s : ℕ}

lemma pairwise_zipIdx_snd {β : Type} (l : List β) (k : ℕ) :
    (l.zipIdx k).Pairwise (fun a b => a.2 < b.2) := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    rw [List.zipIdx_cons, List.pairwise_cons]
    refine ⟨fun p hp => ?_, ih (k + 1)⟩
    have := List.le_snd_of_mem_zipIdx hp
    simp only
    omega

/-- The keys of all records, in enumeration order. -/
noncomputable def recKeys (M : Machine) (s b : ℕ) (HX RX : Xp) (x : List Bool) (ρ : List ℕ)
    (H : ℕ) : List (ℕ × ℕ) :=
  (List.range (numLoc M H)).flatMap fun c =>
    match decodeLoc M H c with
    | some L => (recsOf M s b HX RX x ρ H L).map fun r => ((Loc.code L).val, r.headD 0)
    | none => []

lemma keys_pairwise {b : ℕ} {HX RX : Xp} {x : List Bool} {ρ : List ℕ} {H : ℕ} (hρ : ρ.length = b)
    (hHb : HX.Bnd b) (hRb : RX.Bnd b) (hH : HX.eval ρ = H) (hR : RX.eval ρ = radix M H) :
    (recKeys M s b HX RX x ρ H).Pairwise (fun p q => lexLt p q = true) := by
  have block : ∀ L : Loc M H, ((recsOf M s b HX RX x ρ H L).map fun r =>
      ((Loc.code L).val, r.headD 0)).Pairwise (fun p q => lexLt p q = true) := fun L => by
    obtain ⟨rs, hrs, -⟩ := desc_recsOf (s := s) (x := x) hρ hHb hRb hH hR 0 L
    rw [hrs, List.map_map, List.pairwise_map]
    refine (pairwise_zipIdx_snd rs 0).imp fun h => ?_
    simp only [Function.comp, List.headD_cons, lexLt, decide_eq_true_eq]
    exact Or.inr ⟨trivial, h⟩
  unfold recKeys
  rw [List.pairwise_flatMap]
  refine ⟨fun c _ => ?_, ?_⟩
  · cases decodeLoc M H c with
    | none => exact List.Pairwise.nil
    | some L => exact block L
  · refine (List.pairwise_lt_range (n := numLoc M H)).imp fun {c c'} hcc' => ?_
    intro p hp q hq
    cases hd : decodeLoc M H c with
    | none => rw [hd] at hp; simp at hp
    | some L =>
      cases hd' : decodeLoc M H c' with
      | none => rw [hd'] at hq; simp at hq
      | some L' =>
        rw [hd] at hp; rw [hd'] at hq
        obtain ⟨r, -, rfl⟩ := List.mem_map.mp hp
        obtain ⟨r', -, rfl⟩ := List.mem_map.mp hq
        simp only [lexLt, decide_eq_true_eq, code_of_decodeLoc hd, code_of_decodeLoc hd']
        omega

end Lax119563Proofs.Reduction
