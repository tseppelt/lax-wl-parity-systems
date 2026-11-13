import Lax119563Proofs.Circuits.TimeSimulation

/-!
# The location list of the verifier has no repetitions

So `(allLocs M H).dedup = allLocs M H`, and the commands of `timeProgram` are those of the
moves of the locations of `allLocs` in list order.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine

variable {M : Machine} {H : ℕ}

lemma nodup_allBool : allBool.Nodup := by simp [allBool]
lemma nodup_allOptBool : allOptBool.Nodup := by simp [allOptBool]
lemma nodup_allCV : (allCV M).Nodup := (List.nodup_finRange _).product nodup_allBool
lemma nodup_allExt : (allExt M).Nodup := (List.nodup_finRange _).product nodup_allOptBool
lemma nodup_allFun (m n : ℕ) : (allFun m n).Nodup :=
  (List.nodup_finRange _).map (Equiv.injective _)
lemma nodup_allRows : (allRows M).Nodup :=
  nodup_allExt.product ((nodup_allFun _ _).product (nodup_allFun _ _))

lemma nodup_app {l₁ l₂ : List (Loc M H)} {t : ℕ}
    (h₁ : l₁.Nodup ∧ ∀ a ∈ l₁, (Loc.tuple a).1 < t) (h₂ : l₂.Nodup)
    (ht₂ : ∀ a ∈ l₂, (Loc.tuple a).1 = t) :
    (l₁ ++ l₂).Nodup ∧ ∀ a ∈ l₁ ++ l₂, (Loc.tuple a).1 < t + 1 := by
  refine ⟨h₁.1.append h₂ ?_, ?_⟩
  · intro a ha hb
    have := h₁.2 a ha
    rw [ht₂ a hb] at this
    omega
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · have := h₁.2 a ha; omega
    · rw [ht₂ a ha]; omega

lemma tag_map {α : Type} {L : List α} {f : α → Loc M H} {t : ℕ} (hf : ∀ y, (Loc.tuple (f y)).1 = t) :
    ∀ a ∈ L.map f, (Loc.tuple a).1 = t := by
  intro a ha
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp ha
  exact hf y

theorem nodup_allLocs : (allLocs M H).Nodup := by
  have F := List.nodup_finRange
  unfold allLocs
  have h0 : ([Loc.accept, Loc.reject, Loc.query] : List (Loc M H)).Nodup ∧
      ∀ a ∈ ([Loc.accept, Loc.reject, Loc.query] : List (Loc M H)), (Loc.tuple a).1 < 3 := by
    refine ⟨by simp, ?_⟩
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> simp [Loc.tuple]
  refine (nodup_app (nodup_app (nodup_app (nodup_app (nodup_app (nodup_app (nodup_app
    (nodup_app (nodup_app h0 ?_ (tag_map fun _ => rfl)) ?_ (tag_map fun _ => rfl))
    ?_ (tag_map fun _ => rfl)) ?_ (tag_map fun _ => rfl)) ?_ (tag_map fun _ => rfl))
    ?_ (tag_map fun _ => rfl)) ?_ (tag_map fun _ => rfl)) ?_ (tag_map fun _ => rfl))
    ?_ (tag_map fun _ => rfl)).1
  · refine ((F _).product ((F _).product ((F _).product nodup_allCV))).map ?_
    rintro ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩ h; simp_all
  · refine ((F _).product ((F _).product nodup_allExt)).map ?_
    rintro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h; simp_all
  · refine ((F _).product ((F _).product ((F _).product (F _)))).map ?_
    rintro ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩ h; simp_all
  · refine ((F _).product ((F _).product ((F _).product (F _)))).map ?_
    rintro ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩ h; simp_all
  · refine ((F _).product ((F _).product ((F _).product (nodup_allCV.product (F _))))).map ?_
    rintro ⟨a1, a2, a3, a4, a5⟩ ⟨b1, b2, b3, b4, b5⟩ h; simp_all
  · refine ((F _).product ((F _).product ((F _).product (nodup_allCV.product (F _))))).map ?_
    rintro ⟨a1, a2, a3, a4, a5⟩ ⟨b1, b2, b3, b4, b5⟩ h; simp_all
  · refine ((F _).product (nodup_allRows.product (nodup_allCV.product (F _)))).map ?_
    rintro ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩ h; simp_all
  · refine (nodup_allRows.product (F _)).map ?_
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h; simp_all
  · refine ((F _).product ((F _).product nodup_allCV)).map ?_
    rintro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h; simp_all

theorem dedup_allLocs : (allLocs M H).dedup = allLocs M H :=
  List.dedup_eq_self.mpr nodup_allLocs

end Lax119563Proofs.Reduction
