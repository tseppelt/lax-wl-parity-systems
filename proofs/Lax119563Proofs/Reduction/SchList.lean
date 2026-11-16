import Lax119563Proofs.Reduction.SchemaData

/-!
# The schemas of compiled address programs, numerically

For the register program compiled from an address program, every schema is described by a
`SchNum`: whether it is ternary, the numbers of its locations `locU, locV, locEnd`, and the
mask `msk` of its first permutation (`PermDesc`: block kept, `regVal` XOR-ed with
`shiftVal s ℓ msk`; the other permutations are the identity), together with its domain.
`schNums_compiled`: the schema list of `(compile …).compile p₀ a₀` matches the explicit list
`cmdsN … ++ detN …` (`List.Forall₂ SchMatch`).
-/

open Lax119563.ImplicitParitySystems Lax119563Proofs.Programs Lax119563Proofs.Matrix
open Lax119563Proofs.Circuits

namespace Lax119563Proofs.Reduction

variable {s ℓ : ℕ}

/-- Numbers of a schema. -/
structure SchNum where
  tern : Bool
  u : ℕ
  v : ℕ
  en : ℕ
  msk : ℕ

/-- A binary schema `X → Y` with first permutation of mask `msk`. -/
def binN (X Y msk : ℕ) : SchNum := ⟨false, X, Y, Y, msk⟩

/-- A ternary schema `(A, B, Z)`. -/
def terN (A B Z : ℕ) : SchNum := ⟨true, A, B, Z, 0⟩

/-- The numbers of a one-way gadget. -/
def gadgetN (X msk A B Z Y : ℕ) : List SchNum :=
  [binN X A msk, binN X B msk, terN A B Z, binN Z Y 0]

/-- The permutation keeps blocks and XORs block `i` with `shiftVal s ℓ msk i`. -/
def PermDesc (π : BlockPerm (s + 1) ℓ) (msk : ℕ) : Prop :=
  ∀ c : Coord (s + 1) ℓ, (π.apply c).1 = c.1 ∧
    regVal (π.apply c).2 = regVal c.2 ^^^ shiftVal s ℓ msk c.1.val

/-- The permutation is the identity. -/
def PermId (π : BlockPerm (s + 1) ℓ) : Prop := ∀ c, π.apply c = c

/-- A schema matches its numbers and domain. -/
def SchMatch {N : ℕ} (D : Finset (Coord (s + 1) ℓ)) (e : Schema (s + 1) ℓ N) (n : SchNum) :
    Prop :=
  isTern e = n.tern ∧ (locU e).val = n.u ∧ (locV e).val = n.v ∧ (locEnd e).val = n.en ∧
    PermDesc (permU e) n.msk ∧ PermId (permV e) ∧ PermId (permEnd e) ∧ e.domain = D

lemma xorFields_zero : ∀ s : ℕ, xorFields ℓ s 0 = 0
  | 0 => rfl
  | s + 1 => by simp [xorFields, xorFields_zero s, field]

lemma shiftVal_zero (i : ℕ) : shiftVal s ℓ 0 i = 0 := by
  unfold shiftVal
  split_ifs
  · simp [field]
  · exact xorFields_zero s

lemma permId_id : PermId (idPerm s ℓ) := by
  intro c
  simp [BlockPerm.apply, idPerm]

lemma permDesc_id : PermDesc (idPerm s ℓ) 0 := by
  intro c
  rw [permId_id c, shiftVal_zero, Nat.xor_zero]
  exact ⟨rfl, rfl⟩

lemma permDesc_update (m : ℕ) : PermDesc (updatePerm (toUpdate m : Update s ℓ)) m :=
  fun c => updatePerm_toUpdate_apply m c

lemma gadget_match {N : ℕ} (X : Fin N) (π : BlockPerm (s + 1) ℓ) (msk : ℕ) (hπ : PermDesc π msk)
    (A B Z Y : Fin N) (D : Finset (Coord (s + 1) ℓ)) :
    List.Forall₂ (SchMatch D) (gadget X π A B Z Y D) (gadgetN X.val msk A.val B.val Z.val Y.val) := by
  simp only [gadget, gadgetN, List.forall₂_cons, binN, terN]
  refine ⟨⟨rfl, rfl, rfl, rfl, hπ, permId_id, permId_id, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, hπ, permId_id, permId_id, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, permDesc_id, permId_id, permId_id, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, permDesc_id, permId_id, permId_id, rfl⟩, List.Forall₂.nil⟩

lemma forall₂_flatMap {α β γ δ : Type} {R : γ → δ → Prop} {f : α → List γ} {g : β → List δ} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ (fun a b => List.Forall₂ R (f a) (g b)) l l' →
      List.Forall₂ R (l.flatMap f) (l'.flatMap g)
  | [], [], _ => List.Forall₂.nil
  | _ :: _, _ :: _, List.Forall₂.cons h t => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact List.rel_append h (forall₂_flatMap t)

section Commands

variable {L : Type} {N : ℕ} (code : L → Fin N)

/-- The numbers of the schemas of command `j` (locations of `N` control locations first). -/
def cmdN (j : ℕ) : ACmd L s → List SchNum
  | .assign p _ m q => gadgetN (code q).val m (N + (0 + 8 * j)) (N + (1 + 8 * j))
      (N + (2 + 8 * j)) (code p).val
  | .fork p _ q q' => gadgetN (code q).val 0 (N + (0 + 8 * j)) (N + (1 + 8 * j))
      (N + (2 + 8 * j)) (N + (6 + 8 * j)) ++
    gadgetN (code q').val 0 (N + (3 + 8 * j)) (N + (4 + 8 * j)) (N + (5 + 8 * j))
      (N + (7 + 8 * j)) ++ [terN (N + (6 + 8 * j)) (N + (7 + 8 * j)) (code p).val]

/-- The guard of a command. -/
def _root_.Lax119563Proofs.Circuits.ACmd.guard : ACmd L s → (Fin s → ℕ → Bool)
  | .assign _ g _ _ => g
  | .fork _ g _ _ => g

/-- The source of a command. -/
def _root_.Lax119563Proofs.Circuits.ACmd.src : ACmd L s → L
  | .assign p _ _ _ => p
  | .fork p _ _ _ => p

variable (acc rej : L) (hne : code acc ≠ code rej) (cmds : List (ACmd L s))

/-- The domain of the schemas of a command. -/
def cmdDom (cmd : ACmd L s) : Finset (Coord (s + 1) ℓ) :=
  guardDomain (toGuard cmd.guard) ((AP (ℓ := ℓ) code acc rej hne cmds).executable (code cmd.src))

/-- The numbers of the detector schemas. -/
def detN (r p₀ : ℕ) : List SchNum :=
  gadgetN p₀ 0 (N + r * 8 + 0) (N + r * 8 + 1) (N + r * 8 + 2) (N + r * 8 + 3)

/-- Closes the location number goals of `cmd_match`. -/
local macro "fin_close" : tactic => `(tactic| first
  | rfl
  | exact (loc_prog_val _ _ _ _ _ _).symm
  | exact loc_prog_val _ _ _ _ _ _
  | (simp only [loc_slot_val, Slot.toFin, AP, compile, Fin.val_zero, Fin.val_one, Fin.val_two,
      Fin.isValue]; omega)
  | (simp [loc_slot_val, Slot.toFin, AP, compile]))

lemma cmd_match (j : Fin (AP (ℓ := ℓ) code acc rej hne cmds).commands.length)
    (cmd : ACmd L s) :
    List.Forall₂ (fun e n => SchMatch (cmdDom (ℓ := ℓ) code acc rej hne cmds cmd) e n)
      ((AP (ℓ := ℓ) code acc rej hne cmds).commandSchemas j (cmd.toCmd code))
      (cmdN code j.val cmd) := by
  cases cmd with
  | assign p g m q =>
    rw [commandSchemas_assign]
    have := gadget_match (s := s) (ℓ := ℓ) ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.prog (code q)))
      _ m (permDesc_update m) ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.slot j .a1))
      ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.slot j .b1))
      ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.slot j .z1))
      ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.prog (code p)))
      (guardDomain (toGuard g) ((AP (ℓ := ℓ) code acc rej hne cmds).executable (code p)))
    simp only [cmdN]
    convert this using 2 <;> fin_close
  | fork p g q q' =>
    rw [commandSchemas_fork]
    refine List.rel_append (List.rel_append ?_ ?_) ?_
    · have := gadget_match (s := s) (ℓ := ℓ) ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.prog (code q)))
        _ 0 permDesc_id ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.slot j .a1))
        ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.slot j .b1))
        ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.slot j .z1))
        ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.slot j .out1))
        (guardDomain (toGuard g) ((AP (ℓ := ℓ) code acc rej hne cmds).executable (code p)))
      convert this using 2 <;> fin_close
    · have := gadget_match (s := s) (ℓ := ℓ) ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.prog (code q')))
        _ 0 permDesc_id ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.slot j .a2))
        ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.slot j .b2))
        ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.slot j .z2))
        ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.slot j .out2))
        (guardDomain (toGuard g) ((AP (ℓ := ℓ) code acc rej hne cmds).executable (code p)))
      convert this using 2 <;> fin_close
    · refine List.Forall₂.cons ⟨rfl, ?_, ?_, ?_, permDesc_id, permId_id, permId_id, rfl⟩
        List.Forall₂.nil
      all_goals simp only [locU, locV, locEnd, terN]
      all_goals fin_close

/-- **The schemas of a compiled address program, numerically.** -/
theorem schemas_match (p₀ : Fin (AP (ℓ := ℓ) code acc rej hne cmds).numLocations) (a₀ : Fin s → Fin ℓ → ZMod 2) :
    List.Forall₂ (fun e (n : Finset (Coord (s + 1) ℓ) × SchNum) => SchMatch n.1 e n.2)
      ((AP (ℓ := ℓ) code acc rej hne cmds).compiledSchemas p₀ a₀)
      ((cmds.zipIdx.flatMap fun p => (cmdN code p.2 p.1).map
          fun n => (cmdDom (ℓ := ℓ) code acc rej hne cmds p.1, n)) ++
        (detN (N := N) cmds.length p₀.val).map fun n =>
          (guardDomain (RegisterProgram.queryGuard a₀) true, n)) := by
  refine List.rel_append (forall₂_flatMap ?_) ?_
  · rw [List.forall₂_iff_get]
    have hl : (AP (ℓ := ℓ) code acc rej hne cmds).commands.length = cmds.length := by
      simp only [AP_commands]; exact List.length_map _
    refine ⟨by rw [List.length_finRange, List.length_zipIdx, hl], fun i h1 h2 => ?_⟩
    have hi : i < cmds.length := by rwa [List.length_zipIdx] at h2
    have hc : (AP (ℓ := ℓ) code acc rej hne cmds).commands[i]'(by rw [hl]; exact hi) =
        (cmds[i]'hi).toCmd code := by
      simp only [AP_commands]; exact List.getElem_map _
    simp only [List.get_eq_getElem, List.getElem_finRange, List.getElem_zipIdx, zero_add,
      Fin.getElem_fin, Fin.val_cast]
    rw [hc, List.forall₂_map_right_iff]
    exact cmd_match code acc rej hne cmds _ _
  · rw [List.forall₂_map_right_iff]
    have := gadget_match ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.prog p₀)) (idPerm s ℓ) 0
      permDesc_id ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.det .u1))
      ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.det .u2))
      ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.det .z))
      ((AP (ℓ := ℓ) code acc rej hne cmds).loc (.det .out))
      (guardDomain (RegisterProgram.queryGuard a₀) true)
    simp only [detN, RegisterProgram.detectorSchemas]
    convert this using 2 <;> first
      | exact (loc_prog_val _ _ _ _ _ _).symm
      | (simp [loc_det_val, DetSlot.toFin, AP, compile])

end Commands

end Lax119563Proofs.Reduction
