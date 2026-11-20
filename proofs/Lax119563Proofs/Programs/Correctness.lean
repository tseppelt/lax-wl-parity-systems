import Lax119563Proofs.Programs.Compile
import Lax119563Proofs.Programs.Propagation

/-!
# Correctness of the compiled implicit parity system

For a register program `R` and a query `(p₀, a₀)`, the implicit parity system
`R.compile p₀ a₀` has a conflict if and only if the query accepts.

* If `(p, a)` accepts, then unit propagation derives `Y_{p, E(a)} = 0`, by induction on the
  derivation of acceptance: each one-way gadget transmits the value `0` from its input to its
  output in three rounds, and a fork schema combines the two branch values. For the query,
  the detector then derives `z = 0`, while `z = 1` follows from the initialization of `o`.
* Conversely, if the query does not accept, we exhibit a partial assignment that contains the
  initial facts and is closed under every equation: control locations carry `0` exactly at
  accepting configurations, and the gadget locations carry the values forced by them. Every
  derived fact belongs to this partial assignment, so no conflict occurs.
-/

open Lax119563.ImplicitParitySystems Lax119563.ParitySystems

namespace Lax119563Proofs.Programs

variable {s ℓ : ℕ}

/-! ### Generic facts about gadgets -/

section Gadget

variable {N : ℕ} {X A B Z Y : Fin N} {π : BlockPerm (s + 1) ℓ} {D : Finset (Coord (s + 1) ℓ)}

theorem gadget_domain : ∀ e ∈ gadget X π A B Z Y D, e.domain = D := by
  simp only [gadget, List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl | rfl | rfl) <;> rfl

/-- In a parity system containing the equations of a gadget at the address `x`, the value `0`
at its input propagates to `Z` in two rounds and to the output in three rounds. -/
theorem gadget_propagate {P : ParitySystem (Fin N × (Fin (s + 1) → BlockCoord ℓ))}
    {x : Fin (s + 1) → BlockCoord ℓ}
    (hsub : ∀ e ∈ gadget X π A B Z Y D, e.equation x ∈ P.equations) (hXA : X ≠ A) (hXB : X ≠ B)
    (hAB : A ≠ B) (hAZ : A ≠ Z) (hBZ : B ≠ Z) (hZY : Z ≠ Y) {r : ℕ}
    (hX : ((X, π.act x), 0) ∈ P.known r) :
    ((Z, x), 0) ∈ P.known (r + 2) ∧ ((Y, x), 0) ∈ P.known (r + 3) := by
  have h1 := hsub (.binary X A D π (idPerm s ℓ)) (by simp [gadget])
  have h2 := hsub (.binary X B D π (idPerm s ℓ)) (by simp [gadget])
  have h3 := hsub (.ternary A B Z D (idPerm s ℓ) (idPerm s ℓ) (idPerm s ℓ)) (by simp [gadget])
  have h4 := hsub (.binary Z Y D (idPerm s ℓ) (idPerm s ℓ)) (by simp [gadget])
  simp only [Schema.equation, idPerm_act] at h1 h2 h3 h4
  have hA := ParitySystem.known_pair _ (by simp [hXA]) h1 hX
  have hB := ParitySystem.known_pair _ (by simp [hXB]) h2 hX
  have hZ := ParitySystem.known_triple _ (by simp [hAB]) (by simp [hAZ]) (by simp [hBZ]) h3
    hA hB
  rw [add_zero] at hZ
  exact ⟨hZ, ParitySystem.known_pair _ (by simp [hZY]) h4 hZ⟩

/-- In a parity system containing the equations of a gadget at the address `x`, a value at the
output propagates to `Z` in one round. -/
theorem gadget_back {P : ParitySystem (Fin N × (Fin (s + 1) → BlockCoord ℓ))}
    {x : Fin (s + 1) → BlockCoord ℓ}
    (hsub : ∀ e ∈ gadget X π A B Z Y D, e.equation x ∈ P.equations) (hZY : Z ≠ Y) {r : ℕ}
    {b : ZMod 2} (hY : ((Y, x), b) ∈ P.known r) : ((Z, x), b) ∈ P.known (r + 1) := by
  have h4 := hsub (.binary Z Y D (idPerm s ℓ) (idPerm s ℓ)) (by simp [gadget])
  simp only [Schema.equation, idPerm_act] at h4
  rw [Finset.pair_comm] at h4
  exact ParitySystem.known_pair _ (by simp [hZY.symm]) h4 hY

/-- A partial assignment with the values forced by a gadget is closed under its equations,
provided its input carries at most the value `0`, and only if its output carries `0`. -/
theorem gadget_closed (val : Fin N × (Fin (s + 1) → BlockCoord ℓ) → Option (ZMod 2))
    (hXA : X ≠ A) (hXB : X ≠ B) (hAB : A ≠ B) (hAZ : A ≠ Z) (hBZ : B ≠ Z) (hZY : Z ≠ Y)
    (x : Fin (s + 1) → BlockCoord ℓ)
    (hA : val (A, x) = val (X, π.act x)) (hB : val (B, x) = val (X, π.act x))
    (hZ : val (Z, x) = val (Y, x))
    (h0 : ∀ b, val (X, π.act x) = some b → b = 0 ∧ val (Y, x) = some 0) :
    ∀ e ∈ gadget X π A B Z Y D, ParitySystem.Closed val (e.equation x) := by
  simp only [gadget, List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl | rfl | rfl) <;> simp only [Schema.equation, idPerm_act]
  · exact ParitySystem.closed_pair (by simp [hXA]) hA.symm
  · exact ParitySystem.closed_pair (by simp [hXB]) hB.symm
  · refine ParitySystem.closed_triple (by simp [hAB]) (by simp [hAZ]) (by simp [hBZ])
      ?_ ?_ ?_
    · intro b c hb hc
      rw [hB] at hb
      obtain ⟨rfl, hY⟩ := h0 b hb
      rw [hZ, hY] at hc
      cases hc
      rw [hA, hb]
      rfl
    · intro b c hb hc
      rw [hA] at hb
      obtain ⟨rfl, hY⟩ := h0 b hb
      rw [hZ, hY] at hc
      cases hc
      rw [hB, hb]
      rfl
    · intro b c hb hc
      rw [hA] at hb
      rw [hB, hb] at hc
      cases hc
      obtain ⟨rfl, hY⟩ := h0 b hb
      rw [hZ, hY]
      rfl
  · exact ParitySystem.closed_pair (by simp [hZY]) hZ

end Gadget

namespace RegisterProgram

variable (R : RegisterProgram s ℓ)

/-! ### Completeness: accepting configurations are derived -/

theorem exists_index_of_mem {c : Command s ℓ R.numLocations} (hc : c ∈ R.commands) :
    ∃ j : Fin R.commands.length, R.commands[j] = c := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
  exact ⟨⟨i, hi⟩, rfl⟩

/-- The parity system defined by `R.compile p₀ a₀`, with its variables indexed by
`Fin R.compiledSize`. -/
abbrev compiledParity (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    ParitySystem (Fin R.compiledSize × (Fin (s + 1) → BlockCoord ℓ)) :=
  (R.compile p₀ a₀).toParitySystem

theorem gadget_equations_mem {p₀ : Fin R.numLocations} {a₀ : Fin s → Fin ℓ → ZMod 2}
    {X A B Z Y : Fin R.compiledSize} {π : BlockPerm (s + 1) ℓ} {D : Finset (Coord (s + 1) ℓ)}
    (hsub : ∀ e ∈ gadget X π A B Z Y D, e ∈ R.compiledSchemas p₀ a₀)
    {x : Fin (s + 1) → BlockCoord ℓ} (hx : IsAddress x) (hD : supp x ⊆ D) :
    ∀ e ∈ gadget X π A B Z Y D, e.equation x ∈ (R.compiledParity p₀ a₀).equations :=
  fun e he => ⟨e, hsub e he, x, hx, (gadget_domain e he).symm ▸ hD, rfl⟩

theorem commandSchemas_subset {p₀ : Fin R.numLocations} {a₀ : Fin s → Fin ℓ → ZMod 2}
    {j : Fin R.commands.length} {c : Command s ℓ R.numLocations} (hj : R.commands[j] = c) :
    ∀ e ∈ R.commandSchemas j c, e ∈ R.compiledSchemas p₀ a₀ := by
  intro e he
  exact R.mem_compiledSchemas.2 (Or.inl ⟨j, hj ▸ he⟩)

theorem executable_eq_true {p : Fin R.numLocations} (hacc : p ≠ R.accept)
    (hrej : p ≠ R.reject) : R.executable p = true := by
  simp [executable, hacc, hrej]

/-- If `(p, a)` accepts, then `Y_{p, E(a)} = 0` is derived. -/
theorem known_of_accepts (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2)
    {p : Fin R.numLocations} {a : Fin s → Fin ℓ → ZMod 2} (h : R.Accepts p a) :
    ∃ r, ((R.loc (.prog p), encode a), 0) ∈ (R.compiledParity p₀ a₀).known r := by
  induction h with
  | accept a =>
    exact ⟨0, 0, by simp [compile, compiledInit], rfl, isAddress_encode a, by simp [compile]⟩
  | @assign p q g T a hmem hacc hrej hg _ ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨j, hj⟩ := R.exists_index_of_mem hmem
    rw [← updatePerm_act_encode] at hr
    have hD : supp (encode a) ⊆ guardDomain g (R.executable p) := by
      rw [supp_subset_guardDomain_iff, decode_encode]
      exact ⟨hg, R.executable_eq_true hacc hrej⟩
    exact ⟨r + 3, (gadget_propagate
      (R.gadget_equations_mem (R.commandSchemas_subset hj) (isAddress_encode a) hD)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hr).2⟩
  | @fork p q q' g a hmem hacc hrej hg _ _ ih ih' =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨r', hr'⟩ := ih'
    obtain ⟨j, hj⟩ := R.exists_index_of_mem hmem
    have hsub := R.commandSchemas_subset (p₀ := p₀) (a₀ := a₀) hj
    simp only [commandSchemas, List.mem_append, List.mem_singleton] at hsub
    have hD : supp (encode a) ⊆ guardDomain g (R.executable p) := by
      rw [supp_subset_guardDomain_iff, decode_encode]
      exact ⟨hg, R.executable_eq_true hacc hrej⟩
    rw [← idPerm_act (encode a)] at hr hr'
    have h1 := (gadget_propagate (R.gadget_equations_mem
      (fun e he => hsub e (Or.inl (Or.inl he))) (isAddress_encode a) hD)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (ParitySystem.known_mono _ (le_max_left r r') hr)).2
    have h2 := (gadget_propagate (R.gadget_equations_mem
      (fun e he => hsub e (Or.inl (Or.inr he))) (isAddress_encode a) hD)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (ParitySystem.known_mono _ (le_max_right r r') hr')).2
    have hf : (Schema.ternary (R.loc (.slot j .out1)) (R.loc (.slot j .out2)) (R.loc (.prog p))
        (guardDomain g (R.executable p)) (idPerm s ℓ) (idPerm s ℓ) (idPerm s ℓ)).equation
          (encode a) ∈ (R.compiledParity p₀ a₀).equations :=
      ⟨_, hsub _ (Or.inr rfl), _, isAddress_encode a, hD, rfl⟩
    simp only [Schema.equation, idPerm_act] at hf
    exact ⟨max r r' + 3 + 1, ParitySystem.known_triple _ (by simp) (by simp) (by simp) hf h1 h2⟩

theorem detectorSchemas_subset {p₀ : Fin R.numLocations} {a₀ : Fin s → Fin ℓ → ZMod 2} :
    ∀ e ∈ R.detectorSchemas p₀ a₀, e ∈ R.compiledSchemas p₀ a₀ :=
  fun _ he => R.mem_compiledSchemas.2 (Or.inr he)

/-- If the query accepts, the compiled system has a conflict. -/
theorem hasConflict_of_accepts {p₀ : Fin R.numLocations} {a₀ : Fin s → Fin ℓ → ZMod 2}
    (h : R.Accepts p₀ a₀) : ∃ r, (R.compiledParity p₀ a₀).HasConflict r := by
  obtain ⟨r, hr⟩ := R.known_of_accepts p₀ a₀ h
  have hD : supp (encode a₀) ⊆ guardDomain (queryGuard a₀) true := by
    rw [supp_subset_guardDomain_iff, decode_encode]
    exact ⟨fun i => by simp [queryGuard], rfl⟩
  have hsub := R.gadget_equations_mem (R.detectorSchemas_subset (p₀ := p₀)) (isAddress_encode a₀) hD
  rw [← idPerm_act (encode a₀)] at hr
  have h0 := (gadget_propagate hsub (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) hr).1
  have hout : ((R.loc (.det .out), encode a₀), (1 : ZMod 2)) ∈
      (R.compiledParity p₀ a₀).known 0 :=
    ⟨1, by simp [compile, compiledInit], rfl, isAddress_encode a₀, by simp [compile]⟩
  have h1 := gadget_back hsub (by simp) hout
  exact ⟨r + 2, _, h0, ParitySystem.known_mono _ (by omega) h1⟩

/-! ### Soundness: a closed partial assignment -/

open Classical in
/-- `0` if the configuration `(p, a)` accepts, unknown otherwise. -/
noncomputable def acceptVal (p : Fin R.numLocations) (a : Fin s → Fin ℓ → ZMod 2) :
    Option (ZMod 2) :=
  if R.Accepts p a then some 0 else none

open Classical in
/-- The value of a fork branch location: `0` if the branch target or the fork location accepts. -/
noncomputable def branchVal (p q : Fin R.numLocations) (a : Fin s → Fin ℓ → ZMod 2) :
    Option (ZMod 2) :=
  if R.Accepts q a ∨ R.Accepts p a then some 0 else none

/-- The values at the private locations of a command. -/
noncomputable def slotVal : Command s ℓ R.numLocations → Slot →
    (Fin (s + 1) → BlockCoord ℓ) → Option (ZMod 2)
  | .assign _ _ T q, .a1, x | .assign _ _ T q, .b1, x =>
    R.acceptVal q (decode ((updatePerm T).act x))
  | .assign p _ _ _, .z1, x => R.acceptVal p (decode x)
  | .assign _ _ _ _, _, _ => none
  | .fork _ _ q _, .a1, x | .fork _ _ q _, .b1, x => R.acceptVal q (decode x)
  | .fork p _ q _, .z1, x | .fork p _ q _, .out1, x => R.branchVal p q (decode x)
  | .fork _ _ _ q', .a2, x | .fork _ _ _ q', .b2, x => R.acceptVal q' (decode x)
  | .fork p _ _ q', .z2, x | .fork p _ _ q', .out2, x => R.branchVal p q' (decode x)

/-- The values at a location with the given role. -/
noncomputable def roleVal (p₀ : Fin R.numLocations) :
    Role R.numLocations R.commands.length → (Fin (s + 1) → BlockCoord ℓ) → Option (ZMod 2)
  | .prog p, x => R.acceptVal p (decode x)
  | .slot j t, x => R.slotVal R.commands[j] t x
  | .det .u1, x | .det .u2, x => R.acceptVal p₀ (decode x)
  | .det .z, _ | .det .out, _ => some 1

/-- The closed partial assignment of the compiled system. -/
noncomputable def closedVal (p₀ : Fin R.numLocations) :
    Fin R.compiledSize × (Fin (s + 1) → BlockCoord ℓ) → Option (ZMod 2) :=
  fun v => R.roleVal p₀ ((Role.equivFin _ _).symm v.1) v.2

@[simp] theorem closedVal_loc (p₀ : Fin R.numLocations) (ρ : Role R.numLocations R.commands.length)
    (x : Fin (s + 1) → BlockCoord ℓ) : R.closedVal p₀ (R.loc ρ, x) = R.roleVal p₀ ρ x := by
  simp [closedVal, loc]

theorem acceptVal_eq_some {p : Fin R.numLocations} {a : Fin s → Fin ℓ → ZMod 2} {b : ZMod 2} :
    R.acceptVal p a = some b ↔ R.Accepts p a ∧ b = 0 := by
  unfold acceptVal
  split_ifs with h <;> simp [h, eq_comm]

theorem branchVal_eq_some {p q : Fin R.numLocations} {a : Fin s → Fin ℓ → ZMod 2} {b : ZMod 2} :
    R.branchVal p q a = some b ↔ (R.Accepts q a ∨ R.Accepts p a) ∧ b = 0 := by
  unfold branchVal
  split_ifs with h <;> simp [h, eq_comm]

theorem closed_commandSchemas (p₀ : Fin R.numLocations) (j : Fin R.commands.length)
    {c : Command s ℓ R.numLocations} (hj : R.commands[j] = c) :
    ∀ e ∈ R.commandSchemas j c, ∀ x, supp x ⊆ e.domain →
      ParitySystem.Closed (R.closedVal p₀) (e.equation x) := by
  have hmem : c ∈ R.commands := hj ▸ List.getElem_mem _
  cases c with
  | assign p g T q =>
    intro e he x hx
    rw [gadget_domain e he, supp_subset_guardDomain_iff] at hx
    obtain ⟨hg, hex⟩ := hx
    simp only [executable, decide_eq_true_eq] at hex
    refine gadget_closed _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) x
      ?_ ?_ ?_ ?_ e he
    · simp [roleVal, hj, slotVal]
    · simp [roleVal, hj, slotVal]
    · simp [roleVal, hj, slotVal]
    · intro b hb
      simp only [closedVal_loc, roleVal, acceptVal_eq_some, decode_updatePerm_act] at hb ⊢
      exact ⟨hb.2, Accepts.assign hmem hex.1 hex.2 hg hb.1, trivial⟩
  | fork p g q q' =>
    simp only [commandSchemas, List.mem_append, List.mem_singleton]
    rintro e ((he | he) | rfl) x hx
    · rw [gadget_domain e he, supp_subset_guardDomain_iff] at hx
      refine gadget_closed _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) x
        ?_ ?_ ?_ ?_ e he
      · simp [roleVal, hj, slotVal]
      · simp [roleVal, hj, slotVal]
      · simp [roleVal, hj, slotVal]
      · intro b hb
        simp only [closedVal_loc, roleVal, idPerm_act, acceptVal_eq_some, hj, slotVal,
          branchVal_eq_some] at hb ⊢
        exact ⟨hb.2, Or.inl hb.1, trivial⟩
    · rw [gadget_domain e he, supp_subset_guardDomain_iff] at hx
      refine gadget_closed _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) x
        ?_ ?_ ?_ ?_ e he
      · simp [roleVal, hj, slotVal]
      · simp [roleVal, hj, slotVal]
      · simp [roleVal, hj, slotVal]
      · intro b hb
        simp only [closedVal_loc, roleVal, idPerm_act, acceptVal_eq_some, hj, slotVal,
          branchVal_eq_some] at hb ⊢
        exact ⟨hb.2, Or.inl hb.1, trivial⟩
    · simp only [Schema.domain, supp_subset_guardDomain_iff, executable,
        decide_eq_true_eq] at hx
      obtain ⟨hg, hex⟩ := hx
      simp only [Schema.equation, idPerm_act]
      refine ParitySystem.closed_triple (by simp) (by simp) (by simp) ?_ ?_ ?_ <;>
        intro b c hb hc <;>
        simp only [closedVal_loc, roleVal, hj, slotVal, acceptVal_eq_some,
          branchVal_eq_some] at hb hc ⊢
      · obtain ⟨hp, rfl⟩ := hc
        obtain ⟨-, rfl⟩ := hb
        exact ⟨Or.inr hp, rfl⟩
      · obtain ⟨hp, rfl⟩ := hc
        obtain ⟨-, rfl⟩ := hb
        exact ⟨Or.inr hp, rfl⟩
      · obtain ⟨h1, rfl⟩ := hb
        obtain ⟨h2, rfl⟩ := hc
        refine ⟨?_, rfl⟩
        rcases h1 with h1 | h1
        · rcases h2 with h2 | h2
          · exact Accepts.fork hmem hex.1 hex.2 hg h1 h2
          · exact h2
        · exact h1

theorem closed_detectorSchemas {p₀ : Fin R.numLocations} {a₀ : Fin s → Fin ℓ → ZMod 2}
    (h : ¬ R.Accepts p₀ a₀) :
    ∀ e ∈ R.detectorSchemas p₀ a₀, ∀ x, supp x ⊆ e.domain →
      ParitySystem.Closed (R.closedVal p₀) (e.equation x) := by
  intro e he x hx
  rw [gadget_domain e he, supp_subset_guardDomain_iff] at hx
  have hx' : decode x = a₀ := funext fun i => by simpa [queryGuard] using hx.1 i
  refine gadget_closed _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) x
    ?_ ?_ ?_ ?_ e he
  · simp [roleVal]
  · simp [roleVal]
  · simp [roleVal]
  · intro b hb
    simp only [closedVal_loc, roleVal, idPerm_act, acceptVal_eq_some, hx'] at hb
    exact absurd hb.1 h

/-- If the query does not accept, the compiled system has no conflict. -/
theorem not_hasConflict {p₀ : Fin R.numLocations} {a₀ : Fin s → Fin ℓ → ZMod 2}
    (h : ¬ R.Accepts p₀ a₀) (r : ℕ) : ¬ (R.compiledParity p₀ a₀).HasConflict r := by
  refine ParitySystem.not_hasConflict_of_closed _ (R.closedVal p₀) ?_ ?_ r
  · rintro ⟨⟨v, x⟩, b⟩ ⟨b', hinit, rfl, -, -⟩
    simp only [compile, compiledInit] at hinit
    split_ifs at hinit with h1 h2
    · cases hinit
      subst h1
      simpa [roleVal, acceptVal_eq_some] using Accepts.accept (R := R) (decode x)
    · cases hinit
      subst h2
      simp [roleVal]
  · rintro _ ⟨e, he, x, -, hx, rfl⟩
    rcases R.mem_compiledSchemas.1 he with ⟨j, he⟩ | he
    · exact R.closed_commandSchemas p₀ j rfl e he x hx
    · exact R.closed_detectorSchemas h e he x hx

/-! ### Main statements -/

/-- **Program correctness and query detection.** The compiled implicit parity system has a
conflict if and only if the query `(p₀, a₀)` accepts. -/
theorem conflictRound_compile_lt_top_iff (p₀ : Fin R.numLocations)
    (a₀ : Fin s → Fin ℓ → ZMod 2) :
    (R.compile p₀ a₀).conflictRound < ⊤ ↔ R.Accepts p₀ a₀ := by
  rw [ImplicitParitySystem.conflictRound, ParitySystem.conflictRound_lt_top_iff]
  constructor
  · rintro ⟨r, hr⟩
    by_contra h
    exact R.not_hasConflict h r hr
  · exact R.hasConflict_of_accepts

end RegisterProgram

end Lax119563Proofs.Programs
