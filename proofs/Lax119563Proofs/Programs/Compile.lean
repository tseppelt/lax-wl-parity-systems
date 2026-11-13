import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Basic
import Lax119563Proofs.Programs.Encoding

/-!
# The implicit parity system of a register program and a query

For a register program `R` with `s` registers over `𝔽₂^ℓ`, `w` control locations and `r`
commands, and a query `(p₀, a₀)`, we construct the implicit parity system `I_{R,*}` with
`k = s + 1` blocks. Its locations are

* one location `Y_p` per control location `p` of `R`;
* eight private locations per command (the assignment gadget uses three of them, a fork uses
  all eight: two one-way gadgets with three internal locations each, and the two branch
  locations `b₁, b₂`);
* four locations of the query detector.

Every location has the full coordinate domain. A *one-way gadget* from `X` to `Y` consists of
the four equation schemas `X + A = 0`, `X + B = 0`, `A + B + Z = 0`, `Z + Y = 0` on fresh
locations `A, B, Z`: a value `X = 0` propagates to `Y = 0`, but no value propagates from `Y`
back to `X`.

* An assignment `when p, φ: a ← T(a); goto q` gives a gadget from `Y_q` (at the address
  `π_T E(a) = E(T(a))`) to `Y_p` (at `E(a)`).
* A fork `when p, φ: fork q and q'` gives gadgets from `Y_q` to `b₁` and from `Y_{q'}` to `b₂`
  and the fork schema `b₁ + b₂ + Y_p = 0`.
* The detector is a gadget from `Y_{p₀}` to a location `o` initialized to `1`, guarded by
  `a = a₀`.

All schemas of a command are guarded by the command's guard; commands at `accept` or `reject`
get an empty domain, so they contribute no equations. The location `Y_accept` is initialized
to `0`.
-/

open Lax119563.ImplicitParitySystems

namespace Lax119563Proofs.Programs

/-! ### Locations -/

/-- The eight private locations of a command. -/
inductive Slot
  | a1 | b1 | z1 | a2 | b2 | z2 | out1 | out2
  deriving DecidableEq

/-- The four locations of the query detector. -/
inductive DetSlot
  | u1 | u2 | z | out
  deriving DecidableEq

/-- Numbering of the private locations of a command. -/
def Slot.toFin : Slot → Fin 8
  | a1 => 0 | b1 => 1 | z1 => 2 | a2 => 3 | b2 => 4 | z2 => 5 | out1 => 6 | out2 => 7

/-- Numbering of the locations of the query detector. -/
def DetSlot.toFin : DetSlot → Fin 4
  | u1 => 0 | u2 => 1 | z => 2 | out => 3

/-- The locations of the compiled system: control locations of the program, private locations
of the commands, and locations of the detector. -/
inductive Role (w r : ℕ)
  | prog (p : Fin w)
  | slot (j : Fin r) (t : Slot)
  | det (t : DetSlot)
  deriving DecidableEq

namespace Role

variable {w r : ℕ}

/-- The owner of a location: `none` for control locations, `some (some j)` for the private
locations of command `j`, `some none` for the detector. -/
def key : Role w r → Option (Option (Fin r))
  | prog _ => none
  | slot j _ => some (some j)
  | det _ => some none

/-- The locations as a sum type. -/
def toSum : Role w r → (Fin w ⊕ Fin r × Fin 8) ⊕ Fin 4
  | prog p => .inl (.inl p)
  | slot j t => .inl (.inr (j, t.toFin))
  | det t => .inr t.toFin

/-- Inverse of `toSum`. -/
def ofSum : (Fin w ⊕ Fin r × Fin 8) ⊕ Fin 4 → Role w r
  | .inl (.inl p) => prog p
  | .inl (.inr (j, t)) => slot j (![Slot.a1, .b1, .z1, .a2, .b2, .z2, .out1, .out2] t)
  | .inr t => det (![DetSlot.u1, .u2, .z, .out] t)

/-- The numbering of the locations `Role w r ≃ Fin (w + 8r + 4)`. -/
def equivFin (w r : ℕ) : Role w r ≃ Fin (w + r * 8 + 4) :=
  (Equiv.mk toSum ofSum
      (by intro x; cases x with
        | prog => rfl
        | slot j t => cases t <;> rfl
        | det t => cases t <;> rfl)
      (by rintro ((p | ⟨j, t⟩) | t)
          · rfl
          · fin_cases t <;> rfl
          · fin_cases t <;> rfl)).trans
    ((Equiv.sumCongr (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv) (Equiv.refl _)).trans
      ((Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv))

end Role

variable {s ℓ : ℕ}

/-! ### Schemas -/

section Schemas

variable {N : ℕ}

/-- The one-way gadget from `X` (read at the address `π a`) to `Y` with internal locations
`A, B, Z`, guarded by the coordinate domain `D`. -/
def gadget (X : Fin N) (π : BlockPerm (s + 1) ℓ) (A B Z Y : Fin N)
    (D : Finset (Coord (s + 1) ℓ)) : List (Schema (s + 1) ℓ N) :=
  [.binary X A D π (idPerm s ℓ), .binary X B D π (idPerm s ℓ),
    .ternary A B Z D (idPerm s ℓ) (idPerm s ℓ) (idPerm s ℓ),
    .binary Z Y D (idPerm s ℓ) (idPerm s ℓ)]

end Schemas

namespace RegisterProgram

variable (R : RegisterProgram s ℓ)

/-- The number `w + 8r + 4` of locations of the compiled system. -/
abbrev compiledSize : ℕ := R.numLocations + R.commands.length * 8 + 4

/-- The location of the compiled system with the given role. -/
def loc (ρ : Role R.numLocations R.commands.length) : Fin R.compiledSize :=
  Role.equivFin _ _ ρ

/-- Commands at the location `p` are executed: `p` is neither `accept` nor `reject`. -/
def executable (p : Fin R.numLocations) : Bool :=
  decide (p ≠ R.accept ∧ p ≠ R.reject)

/-- The schemas of command number `j`. -/
def commandSchemas (j : Fin R.commands.length) :
    Command s ℓ R.numLocations → List (Schema (s + 1) ℓ R.compiledSize)
  | .assign p g T q =>
    gadget (R.loc (.prog q)) (updatePerm T) (R.loc (.slot j .a1)) (R.loc (.slot j .b1))
      (R.loc (.slot j .z1)) (R.loc (.prog p)) (guardDomain g (R.executable p))
  | .fork p g q q' =>
    gadget (R.loc (.prog q)) (idPerm s ℓ) (R.loc (.slot j .a1)) (R.loc (.slot j .b1))
      (R.loc (.slot j .z1)) (R.loc (.slot j .out1)) (guardDomain g (R.executable p)) ++
    gadget (R.loc (.prog q')) (idPerm s ℓ) (R.loc (.slot j .a2)) (R.loc (.slot j .b2))
      (R.loc (.slot j .z2)) (R.loc (.slot j .out2)) (guardDomain g (R.executable p)) ++
    [.ternary (R.loc (.slot j .out1)) (R.loc (.slot j .out2)) (R.loc (.prog p))
      (guardDomain g (R.executable p)) (idPerm s ℓ) (idPerm s ℓ) (idPerm s ℓ)]

/-- The guard `a = a₀` of the query detector. -/
def queryGuard (a₀ : Fin s → Fin ℓ → ZMod 2) : Guard s ℓ :=
  ⟨fun i => {a₀ i}⟩

/-- The schemas of the query detector. -/
def detectorSchemas (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    List (Schema (s + 1) ℓ R.compiledSize) :=
  gadget (R.loc (.prog p₀)) (idPerm s ℓ) (R.loc (.det .u1)) (R.loc (.det .u2))
    (R.loc (.det .z)) (R.loc (.det .out)) (guardDomain (queryGuard a₀) true)

/-- All schemas of the compiled system. -/
def compiledSchemas (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    List (Schema (s + 1) ℓ R.compiledSize) :=
  (List.finRange R.commands.length).flatMap (fun j => R.commandSchemas j R.commands[j]) ++
    R.detectorSchemas p₀ a₀

/-- The initialization: `0` at `Y_accept`, `1` at the detector output `o`, `⋆` elsewhere. -/
def compiledInit (v : Fin R.compiledSize) : Option (ZMod 2) :=
  if v = R.loc (.prog R.accept) then some 0
  else if v = R.loc (.det .out) then some 1
  else none

@[simp] theorem loc_inj {ρ ρ' : Role R.numLocations R.commands.length} :
    R.loc ρ = R.loc ρ' ↔ ρ = ρ' :=
  (Role.equivFin _ _).apply_eq_iff_eq

/-- The owner of a location of the compiled system, see `Role.key`. -/
def locKey (v : Fin R.compiledSize) : Option (Option (Fin R.commands.length)) :=
  ((Role.equivFin _ _).symm v).key

@[simp] theorem locKey_loc (ρ : Role R.numLocations R.commands.length) :
    R.locKey (R.loc ρ) = ρ.key := by
  simp [locKey, loc]

end RegisterProgram

/-! ### Well-formedness and the meet condition -/

section Meet

variable {k N : ℕ}

/-- Two schemas share at most one location. -/
def Meet (e e' : Schema k ℓ N) : Prop :=
  (e.locations ∩ e'.locations).card ≤ 1

/-- Every location of `e` is `u` or satisfies `Pr`. -/
def HasShape (e : Schema k ℓ N) (u : Fin N) (Pr : Fin N → Prop) : Prop :=
  ∀ x ∈ e.locations, x = u ∨ Pr x

theorem HasShape.mono {e : Schema k ℓ N} {u : Fin N} {Pr Pr' : Fin N → Prop}
    (h : HasShape e u Pr) (hPr : ∀ x, Pr x → Pr' x) : HasShape e u Pr' :=
  fun x hx => (h x hx).imp_right (hPr x)

theorem meet_of_shape {e e' : Schema k ℓ N} {u u' : Fin N} {Pr Pr' : Fin N → Prop}
    (h : HasShape e u Pr) (h' : HasShape e' u' Pr') (hPr : ∀ x, Pr x → x ≠ u' ∧ ¬ Pr' x) :
    Meet e e' := by
  have hu : ∀ x ∈ e.locations ∩ e'.locations, x = u := by
    intro x hx
    rw [Finset.mem_inter] at hx
    rcases h x hx.1 with hx1 | hx1
    · exact hx1
    · rcases h' x hx.2 with hx2 | hx2
      · exact absurd hx2 (hPr x hx1).1
      · exact absurd hx2 (hPr x hx1).2
  exact Finset.card_le_one.2 fun x hx y hy => (hu x hx).trans (hu y hy).symm

/-- All locations of `e` but possibly one location `u` belong to the owner `κ`; the location
`u` belongs to `κ` or to no owner. -/
def Owned {K : Type*} (key : Fin N → Option K) (κ : K) (e : Schema k ℓ N) : Prop :=
  ∃ u, (key u = none ∨ key u = some κ) ∧ HasShape e u fun x => key x = some κ

theorem meet_of_owned {K : Type*} (key : Fin N → Option K) {κ κ' : K} (hκ : κ ≠ κ')
    {e e' : Schema k ℓ N} (h : Owned key κ e) (h' : Owned key κ' e') : Meet e e' := by
  obtain ⟨u, -, hu⟩ := h
  obtain ⟨u', hu', hu'e⟩ := h'
  refine meet_of_shape hu hu'e fun x hx => ⟨?_, ?_⟩
  · rintro rfl
    rcases hu' with h | h <;> rw [hx] at h
    · exact absurd h (by simp)
    · exact hκ (Option.some.inj h)
  · rw [hx]
    exact fun h => hκ (Option.some.inj h)

variable {X A B Z Y : Fin N} {π : BlockPerm (s + 1) ℓ} {D : Finset (Coord (s + 1) ℓ)}

theorem gadget_shape :
    ∀ e ∈ gadget X π A B Z Y D, ∃ u, (u = X ∨ u = Y ∨ u = A) ∧
      HasShape e u fun x => x = A ∨ x = B ∨ x = Z := by
  simp only [gadget, List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl | rfl | rfl)
  · refine ⟨X, by simp, fun x hx => ?_⟩
    simp only [Schema.locations, Finset.mem_insert, Finset.mem_singleton] at hx
    tauto
  · refine ⟨X, by simp, fun x hx => ?_⟩
    simp only [Schema.locations, Finset.mem_insert, Finset.mem_singleton] at hx
    tauto
  · refine ⟨A, by simp, fun x hx => ?_⟩
    simp only [Schema.locations, Finset.mem_insert, Finset.mem_singleton] at hx
    tauto
  · refine ⟨Y, by simp, fun x hx => ?_⟩
    simp only [Schema.locations, Finset.mem_insert, Finset.mem_singleton] at hx
    tauto

theorem gadget_owned {K : Type*} (key : Fin N → Option K) (κ : K)
    (hX : key X = none ∨ key X = some κ) (hY : key Y = none ∨ key Y = some κ)
    (hA : key A = some κ) (hB : key B = some κ) (hZ : key Z = some κ) :
    ∀ e ∈ gadget X π A B Z Y D, Owned key κ e := by
  intro e he
  obtain ⟨u, hu, hshape⟩ := gadget_shape e he
  refine ⟨u, ?_, hshape.mono ?_⟩
  · rcases hu with rfl | rfl | rfl
    · exact hX
    · exact hY
    · exact Or.inr hA
  · rintro x (rfl | rfl | rfl) <;> assumption

theorem gadget_pairwise (hAB : A ≠ B) (hAZ : A ≠ Z) (hBZ : B ≠ Z) (hXA : X ≠ A) (hXB : X ≠ B)
    (hXZ : X ≠ Z) (hYA : Y ≠ A) (hYB : Y ≠ B) (hYZ : Y ≠ Z) :
    (gadget X π A B Z Y D).Pairwise Meet := by
  simp only [gadget, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
  · refine Finset.card_le_one.2 fun a ha b hb => ?_
    simp only [Schema.locations, Finset.mem_inter, Finset.mem_insert,
      Finset.mem_singleton] at ha hb
    grind

theorem gadget_wellFormed (hXA : X ≠ A) (hXB : X ≠ B) (hAB : A ≠ B) (hAZ : A ≠ Z)
    (hBZ : B ≠ Z) (hZY : Z ≠ Y) :
    ∀ e ∈ gadget X π A B Z Y D, e.WellFormed fun _ => Finset.univ := by
  simp only [gadget, List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl | rfl | rfl) <;> simp [Schema.WellFormed, *]

end Meet

namespace RegisterProgram

variable (R : RegisterProgram s ℓ)

theorem commandSchemas_wellFormed (j : Fin R.commands.length) (c : Command s ℓ R.numLocations) :
    ∀ e ∈ R.commandSchemas j c, e.WellFormed fun _ => Finset.univ := by
  cases c with
  | assign p g T q =>
    exact gadget_wellFormed (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  | fork p g q q' =>
    simp only [commandSchemas, List.mem_append, List.mem_singleton]
    rintro e ((he | he) | rfl)
    · exact gadget_wellFormed (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) e he
    · exact gadget_wellFormed (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) e he
    · simp [Schema.WellFormed]

theorem commandSchemas_owned (j : Fin R.commands.length) (c : Command s ℓ R.numLocations) :
    ∀ e ∈ R.commandSchemas j c, Owned R.locKey (some j) e := by
  cases c with
  | assign p g T q =>
    exact gadget_owned _ _ (by simp [Role.key]) (by simp [Role.key]) (by simp [Role.key])
      (by simp [Role.key]) (by simp [Role.key])
  | fork p g q q' =>
    simp only [commandSchemas, List.mem_append, List.mem_singleton]
    rintro e ((he | he) | rfl)
    · exact gadget_owned _ _ (by simp [Role.key]) (by simp [Role.key]) (by simp [Role.key])
        (by simp [Role.key]) (by simp [Role.key]) e he
    · exact gadget_owned _ _ (by simp [Role.key]) (by simp [Role.key]) (by simp [Role.key])
        (by simp [Role.key]) (by simp [Role.key]) e he
    · refine ⟨R.loc (.prog p), by simp [Role.key], fun x hx => ?_⟩
      simp only [Schema.locations, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simp [Role.key]

theorem commandSchemas_pairwise (j : Fin R.commands.length) (c : Command s ℓ R.numLocations) :
    (R.commandSchemas j c).Pairwise Meet := by
  cases c with
  | assign p g T q =>
    exact gadget_pairwise (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp)
  | fork p g q q' =>
    simp only [commandSchemas]
    rw [List.pairwise_append, List.pairwise_append]
    refine ⟨⟨gadget_pairwise (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp), gadget_pairwise (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp), ?_⟩, List.pairwise_singleton _ _, ?_⟩
    · intro e he e' he'
      obtain ⟨u, -, hu⟩ := gadget_shape e he
      obtain ⟨u', hu', hu'e⟩ := gadget_shape e' he'
      refine meet_of_shape hu hu'e ?_
      rcases hu' with rfl | rfl | rfl <;> rintro x (rfl | rfl | rfl) <;> simp
    · intro e he e' he'
      rw [List.mem_singleton] at he'
      subst he'
      have hf : HasShape (Schema.ternary (R.loc (.slot j .out1)) (R.loc (.slot j .out2))
          (R.loc (.prog p)) (guardDomain g (R.executable p)) (idPerm s ℓ) (idPerm s ℓ)
          (idPerm s ℓ)) (R.loc (.prog p))
          (fun x => x = R.loc (.slot j .out1) ∨ x = R.loc (.slot j .out2)) := by
        intro x hx
        simp only [Schema.locations, Finset.mem_insert, Finset.mem_singleton] at hx
        tauto
      rw [List.mem_append] at he
      rcases he with he | he
      · obtain ⟨u, -, hu⟩ := gadget_shape e he
        exact meet_of_shape hu hf (by rintro x (rfl | rfl | rfl) <;> simp)
      · obtain ⟨u, -, hu⟩ := gadget_shape e he
        exact meet_of_shape hu hf (by rintro x (rfl | rfl | rfl) <;> simp)

theorem detectorSchemas_wellFormed (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    ∀ e ∈ R.detectorSchemas p₀ a₀, e.WellFormed fun _ => Finset.univ :=
  gadget_wellFormed (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)

theorem detectorSchemas_owned (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    ∀ e ∈ R.detectorSchemas p₀ a₀, Owned R.locKey none e :=
  gadget_owned _ _ (by simp [Role.key]) (by simp [Role.key]) (by simp [Role.key])
    (by simp [Role.key]) (by simp [Role.key])

theorem detectorSchemas_pairwise (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    (R.detectorSchemas p₀ a₀).Pairwise Meet :=
  gadget_pairwise (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp)

theorem mem_compiledSchemas {p₀ : Fin R.numLocations} {a₀ : Fin s → Fin ℓ → ZMod 2}
    {e : Schema (s + 1) ℓ R.compiledSize} :
    e ∈ R.compiledSchemas p₀ a₀ ↔
      (∃ j : Fin R.commands.length, e ∈ R.commandSchemas j R.commands[j]) ∨
        e ∈ R.detectorSchemas p₀ a₀ := by
  simp [compiledSchemas, List.mem_flatMap]

theorem compiledSchemas_wellFormed (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    ∀ e ∈ R.compiledSchemas p₀ a₀, e.WellFormed fun _ => Finset.univ := by
  intro e he
  rcases R.mem_compiledSchemas.1 he with ⟨j, he⟩ | he
  · exact R.commandSchemas_wellFormed j _ e he
  · exact R.detectorSchemas_wellFormed p₀ a₀ e he

theorem compiledSchemas_pairwise (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    (R.compiledSchemas p₀ a₀).Pairwise Meet := by
  rw [compiledSchemas, List.pairwise_append, List.pairwise_flatMap]
  refine ⟨⟨fun j _ => R.commandSchemas_pairwise j _, ?_⟩, R.detectorSchemas_pairwise p₀ a₀, ?_⟩
  · refine (List.nodup_finRange _).imp fun {j j'} hjj' e he e' he' => ?_
    exact meet_of_owned R.locKey (by simpa using hjj') (R.commandSchemas_owned j _ e he)
      (R.commandSchemas_owned j' _ e' he')
  · intro e he e' he'
    obtain ⟨j, -, he⟩ := List.mem_flatMap.1 he
    exact meet_of_owned R.locKey (by simp) (R.commandSchemas_owned j _ e he)
      (R.detectorSchemas_owned p₀ a₀ e' he')

/-- **The implicit parity system `I_{R,*}`** of the register program `R` and the query
`(p₀, a₀)`, with `k = s + 1` blocks, `w + 8r + 4` locations with full coordinate domains, and
at most `9r + 4` schemas. -/
def compile (p₀ : Fin R.numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    ImplicitParitySystem (s + 1) ℓ where
  numLocations := R.compiledSize
  domain _ := Finset.univ
  schemas := R.compiledSchemas p₀ a₀
  init := R.compiledInit
  schema_wellFormed := R.compiledSchemas_wellFormed p₀ a₀
  schemas_meet := R.compiledSchemas_pairwise p₀ a₀

end RegisterProgram

end Lax119563Proofs.Programs
