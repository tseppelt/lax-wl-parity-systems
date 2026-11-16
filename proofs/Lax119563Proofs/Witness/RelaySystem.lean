import Lax119563Proofs.Witness.Relay

/-!
# The relay counter as an implicit parity system

Well-formedness of the schemas and the pairwise intersection condition, and the definition
`relay k ℓ : ImplicitParitySystem k ℓ`.
-/

open Lax119563.ImplicitParitySystems Lax119563.ParitySystems

namespace Lax119563Proofs.Witness

variable {k ℓ : ℕ}

theorem image_idP (D : Finset (Coord k ℓ)) : D.image (idP : BlockPerm k ℓ).apply = D := by
  have : (idP : BlockPerm k ℓ).apply = id := funext idP_apply
  rw [this, Finset.image_id]

theorem gate_wellFormed (j : Fin (nbits k ℓ)) :
    ∀ e ∈ gate j, e.WellFormed (fun x => domS k ℓ ((locEquiv _).symm x)) := by
  intro e he
  simp only [gate, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;>
    simp [Schema.WellFormed, loc, loc_inj, image_idP, domS]

theorem endpoints_wellFormed :
    ∀ e ∈ endpoints k ℓ, e.WellFormed (fun x => domS k ℓ ((locEquiv _).symm x)) := by
  intro e he
  simp only [endpoints, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;>
    simp [Schema.WellFormed, loc, loc_inj, image_idP, domS]

theorem relay_wellFormed :
    ∀ e ∈ relaySchemas k ℓ, e.WellFormed (fun x => domS k ℓ ((locEquiv _).symm x)) := by
  intro e he
  rcases mem_relaySchemas.mp he with h | ⟨j, h⟩
  · exact endpoints_wellFormed e h
  · exact gate_wellFormed j e h

/-- Every location of a gate schema at `j` is `v` or a private location of `j`. -/
theorem gate_locations {j : Fin (nbits k ℓ)} {e : Schema k ℓ (nlocs k ℓ)} (he : e ∈ gate j)
    {x : Fin (nlocs k ℓ)} (hx : x ∈ e.locations) :
    x = loc k ℓ (.inl 0) ∨ ∃ c, x = loc k ℓ (.inr (j, c)) := by
  simp only [gate, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;>
    simp only [Schema.locations, Finset.mem_insert, Finset.mem_singleton] at hx <;>
    aesop

/-- Every location of an endpoint schema is `v`, `z₀` or `z₁`. -/
theorem endpoints_locations {e : Schema k ℓ (nlocs k ℓ)} (he : e ∈ endpoints k ℓ)
    {x : Fin (nlocs k ℓ)} (hx : x ∈ e.locations) : ∃ i, x = loc k ℓ (.inl i) := by
  simp only [endpoints, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;>
    simp only [Schema.locations, Finset.mem_insert, Finset.mem_singleton] at hx <;>
    aesop

theorem card_inter_le_one_of {s t : Finset (Fin (nlocs k ℓ))}
    (h : ∀ x ∈ s, x ∈ t → x = loc k ℓ (.inl 0)) : (s ∩ t).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_inter] at ha hb
  rw [h a ha.1 ha.2, h b hb.1 hb.2]

theorem gate_pairwise (j : Fin (nbits k ℓ)) :
    (gate j).Pairwise fun e e' : Schema k ℓ (nlocs k ℓ) => (e.locations ∩ e'.locations).card ≤ 1 := by
  simp only [gate]
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_
    (List.pairwise_singleton _ _))) <;>
  · intro e' he'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
    rcases he' with rfl | rfl | rfl <;>
    · rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Schema.locations, Finset.mem_inter, Finset.mem_insert,
        Finset.mem_singleton] at ha hb
      aesop (add norm simp [loc_inj])

theorem common_loc_gate_gate {j j' : Fin (nbits k ℓ)} (hjj : j ≠ j') {e e' : Schema k ℓ (nlocs k ℓ)}
    (he : e ∈ gate j) (he' : e' ∈ gate j') :
    ∀ x ∈ e.locations, x ∈ e'.locations → x = loc k ℓ (.inl 0) := by
  intro x hx hx'
  rcases gate_locations he hx with h | ⟨c, rfl⟩
  · exact h
  rcases gate_locations he' hx' with h | ⟨c', h⟩
  · exact h
  · rw [loc_inj] at h
    simp only [Sum.inr.injEq, Prod.mk.injEq] at h
    exact absurd h.1 hjj

theorem relay_pairwise :
    (relaySchemas k ℓ).Pairwise fun e e' => (e.locations ∩ e'.locations).card ≤ 1 := by
  rw [relaySchemas, List.pairwise_append, List.pairwise_flatMap]
  refine ⟨?_, ⟨fun j _ => gate_pairwise j, ?_⟩, ?_⟩
  · simp only [endpoints]
    refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
    · intro e' he'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
      subst he'
      apply card_inter_le_one_of
      intro x hx hx'
      simp only [Schema.locations, Finset.mem_insert, Finset.mem_singleton] at hx hx'
      rcases hx with rfl | rfl <;> rcases hx' with h | h <;> simp_all [loc_inj]
  · exact (List.nodup_finRange _).imp fun hjj e he e' he' =>
      card_inter_le_one_of (common_loc_gate_gate hjj he he')
  · intro e he e' he'
    obtain ⟨j, -, he'⟩ := List.mem_flatMap.mp he'
    apply card_inter_le_one_of
    intro x hx hx'
    obtain ⟨i, rfl⟩ := endpoints_locations he hx
    rcases gate_locations he' hx' with h | ⟨c, h⟩
    · exact h
    · rw [loc_inj] at h; cases h

/-- **The relay counter** `Î^{k,ℓ}_ctr`, counting down. (Reducible, so that its number of
locations is seen to be `nlocs k ℓ` by `simp`.) -/
@[reducible] def relay (k ℓ : ℕ) : ImplicitParitySystem k ℓ where
  numLocations := nlocs k ℓ
  domain x := domS k ℓ ((locEquiv _).symm x)
  schemas := relaySchemas k ℓ
  init x := initS k ℓ ((locEquiv _).symm x)
  schema_wellFormed := relay_wellFormed
  schemas_meet := relay_pairwise

@[simp] theorem relay_domain (σ) : (relay k ℓ).domain (loc k ℓ σ) = domS k ℓ σ := by
  simp [relay, loc]

@[simp] theorem relay_init (σ) : (relay k ℓ).init (loc k ℓ σ) = initS k ℓ σ := by
  simp [relay, loc]

end Lax119563Proofs.Witness
