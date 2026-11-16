import Lax119563Proofs.Witness.RelaySystem
import Lax119563Proofs.Witness.Counter
import Lax119563Proofs.Witness.Derivation

/-!
# The relay counter has a conflict (Lemma relay-size, `τ < ∞`)

Unit propagation sends `X_{v,s} = 0` (from `X_{z₀,s} = 0`) down the counter: every address
`a ≠ 0` is allowed for the gate of its lowest set bit `j`, which derives
`X_{p_j,a} = X_{q_j,a} = 0`, then `X_{r_j,a} = 0`, then `X_{v,T_j a} = 0`, and `T_j a` has value
one less. After `2^m - 1` gates the zero address carries `X_{v,0} = 0`, while `X_{z₁,0} = 1`
gives `X_{v,0} = 1`.
-/

open Lax119563.ImplicitParitySystems Lax119563.ParitySystems

namespace Lax119563Proofs.Witness

variable {V : Type*} [DecidableEq V]

theorem infer_zero {P : ParitySystem V} {h : Finset V} (hh : h ∈ P.equations) {X : V}
    (hX : X ∈ h) {r : ℕ} (hk : ∀ Y ∈ h, Y ≠ X → (Y, (0 : ZMod 2)) ∈ P.known r) :
    (X, (0 : ZMod 2)) ∈ P.known (r + 1) :=
  Or.inr ⟨h, hh, hX, fun _ => 0, hk, by simp⟩

theorem infer_one {P : ParitySystem V} {X Y : V} (hh : {Y, X} ∈ P.equations) (hne : Y ≠ X)
    {r : ℕ} (hY : (Y, (1 : ZMod 2)) ∈ P.known r) : (X, (1 : ZMod 2)) ∈ P.known (r + 1) := by
  refine Or.inr ⟨{Y, X}, hh, by simp, fun _ => 1, ?_, ?_⟩
  · intro Z hZ hZX
    rw [Finset.mem_insert, Finset.mem_singleton] at hZ
    rcases hZ with rfl | rfl
    · exact hY
    · exact absurd rfl hZX
  · have : ({Y, X} : Finset V).erase X = {Y} := by
      rw [Finset.pair_comm]; exact Finset.erase_insert (by simpa using hne.symm)
    simp [this]

variable {k ℓ : ℕ}

theorem mem_relay_equations {e : Schema k ℓ (nlocs k ℓ)} (he : e ∈ relaySchemas k ℓ)
    {a : Fin k → BlockCoord ℓ} (ha : IsAddress a) (hs : supp a ⊆ e.domain) :
    e.equation a ∈ (relay k ℓ).toParitySystem.equations :=
  ⟨e, he, a, ha, hs, rfl⟩

theorem gate_mem (j : Fin (nbits k ℓ)) {e : Schema k ℓ (nlocs k ℓ)} (he : e ∈ gate j) :
    e ∈ relaySchemas k ℓ :=
  mem_relaySchemas.mpr (Or.inr ⟨j, he⟩)

/-- The main location `v`. -/
abbrev vL (k ℓ : ℕ) : Fin (nlocs k ℓ) := loc k ℓ (.inl 0)

theorem forward : ∀ n, n ≤ 2 ^ nbits k ℓ - 1 → ∃ a : Fin k → BlockCoord ℓ, IsAddress a ∧
    cval a + n = 2 ^ nbits k ℓ - 1 ∧
    ((vL k ℓ, a), (0 : ZMod 2)) ∈ (relay k ℓ).toParitySystem.known (1 + 3 * n) := by
  intro n hn
  induction n with
  | zero =>
    refine ⟨sAddr k ℓ, isAddress_withChecksum _, by have := cval_sAddr (k := k) (ℓ := ℓ); omega,
      ?_⟩
    have hh := mem_relay_equations
      (e := .binary (loc k ℓ (.inl 1)) (loc k ℓ (.inl 0)) (supp (sAddr k ℓ)) idP idP)
      (by simp [relaySchemas, endpoints]) (isAddress_withChecksum _) (subset_refl _)
    simp only [Schema.equation, idP_act] at hh
    refine infer_zero hh (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) fun Y hY hne => ?_
    rw [Finset.mem_insert, Finset.mem_singleton] at hY
    rcases hY with rfl | rfl
    · refine ⟨0, ?_, rfl, isAddress_withChecksum _, ?_⟩
      · show (relay k ℓ).init (loc k ℓ (.inl 1)) = some 0
        rw [relay_init]; rfl
      · show supp (sAddr k ℓ) ⊆ (relay k ℓ).domain (loc k ℓ (.inl 1))
        rw [relay_domain]; exact subset_refl _
    · exact absurd rfl hne
  | succ n ih =>
    obtain ⟨a, ha, hval, hk⟩ := ih (by omega)
    obtain ⟨j, hj, hsupp⟩ := exists_allowed ha (by omega)
    have hdec := cval_decP hj hsupp
    let jj : Fin (nbits k ℓ) := ⟨j, hj⟩
    refine ⟨(decP j).act a, isAddress_act ha, by omega, ?_⟩
    rw [show 1 + 3 * (n + 1) = 1 + 3 * n + 1 + 1 + 1 by ring]
    have mem := fun e (he : e ∈ gate jj) => mem_relay_equations (gate_mem jj he) ha
    have hp : ((loc k ℓ (.inr (jj, 0)), a), (0 : ZMod 2)) ∈
        (relay k ℓ).toParitySystem.known (1 + 3 * n + 1) := by
      have hh := mem (.binary (loc k ℓ (.inl 0))
        (loc k ℓ (.inr (jj, 0))) (relayDom j) idP idP) (by simp [gate, jj]) hsupp
      simp only [Schema.equation, idP_act] at hh
      refine infer_zero hh (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) fun Y hY hne => ?_
      rw [Finset.mem_insert, Finset.mem_singleton] at hY
      rcases hY with rfl | rfl
      · exact hk
      · exact absurd rfl hne
    have hq : ((loc k ℓ (.inr (jj, 1)), a), (0 : ZMod 2)) ∈
        (relay k ℓ).toParitySystem.known (1 + 3 * n + 1) := by
      have hh := mem (.binary (loc k ℓ (.inl 0))
        (loc k ℓ (.inr (jj, 1))) (relayDom j) idP idP) (by simp [gate, jj]) hsupp
      simp only [Schema.equation, idP_act] at hh
      refine infer_zero hh (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) fun Y hY hne => ?_
      rw [Finset.mem_insert, Finset.mem_singleton] at hY
      rcases hY with rfl | rfl
      · exact hk
      · exact absurd rfl hne
    have hr : ((loc k ℓ (.inr (jj, 2)), a), (0 : ZMod 2)) ∈
        (relay k ℓ).toParitySystem.known (1 + 3 * n + 1 + 1) := by
      have hh := mem (.ternary (loc k ℓ (.inr (jj, 0)))
        (loc k ℓ (.inr (jj, 1))) (loc k ℓ (.inr (jj, 2))) (relayDom j) idP idP idP) (by simp [gate, jj]) hsupp
      simp only [Schema.equation, idP_act] at hh
      refine infer_zero hh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _))) fun Y hY hne => ?_
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hY
      rcases hY with rfl | rfl | rfl
      · exact hp
      · exact hq
      · exact absurd rfl hne
    have hh := mem (.binary (loc k ℓ (.inr (jj, 2)))
      (loc k ℓ (.inl 0)) (relayDom j) idP (decP j)) (by simp [gate, jj]) hsupp
    simp only [Schema.equation, idP_act] at hh
    refine infer_zero hh (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) fun Y hY hne => ?_
    rw [Finset.mem_insert, Finset.mem_singleton] at hY
    rcases hY with rfl | rfl
    · exact hr
    · exact absurd rfl hne

/-- The round in which the relay counter has a conflict. -/
theorem relay_hasConflict :
    (relay k ℓ).toParitySystem.HasConflict (1 + 3 * (2 ^ nbits k ℓ - 1)) := by
  obtain ⟨a, ha, hval, hk⟩ := forward (k := k) (ℓ := ℓ) _ le_rfl
  have h0 := eq_zero_of_cval ha (by omega)
  subst h0
  refine ⟨(vL k ℓ, 0), hk, ?_⟩
  refine known_mono _ (by omega : 1 ≤ 1 + 3 * (2 ^ nbits k ℓ - 1)) ?_
  have hh := mem_relay_equations
    (e := .binary (loc k ℓ (.inl 2)) (loc k ℓ (.inl 0)) (supp 0) idP idP)
    (by simp [relaySchemas, endpoints]) (by simp [IsAddress]) (subset_refl _)
  simp only [Schema.equation, idP_act] at hh
  refine infer_one hh (fun h => absurd (loc_inj.mp (congrArg Prod.fst h)) (by simp)) ?_
  refine ⟨1, ?_, rfl, by simp [IsAddress], ?_⟩
  · show (relay k ℓ).init (loc k ℓ (.inl 2)) = some 1
    rw [relay_init]; rfl
  · show supp 0 ⊆ (relay k ℓ).domain (loc k ℓ (.inl 2))
    rw [relay_domain]; exact subset_refl _

end Lax119563Proofs.Witness
