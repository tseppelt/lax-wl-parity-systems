import Lax119563Proofs.Reduction.SysDesc
import Lax119563Proofs.Reduction.Prelude

/-!
# The generator of the system description

`sysGen M s` (run on the globals, depth `14`) emits `systemDescription (Iv M x s ℓ H)`
(**`out_sysGen`**): the header `s + 1, ℓ, W`, for each location its initialization number and
its (full) domain (`locGen`), the number of schemas, and for each schema (schema enumerator,
`schBody`) its kind, locations, domain (`domGen`: loops over the coordinates with the domain
test `violAt`, counted first for the length) and permutations (`permGen`).
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Lax119563.DeterministicTime Xp
open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563Proofs.Programs

namespace Gn

/-- Loops over blocks `i ≤ s` and register values `v < 2^ℓ` (`PX` evaluates to `2^ℓ`; by
`loopX`, so that `inBit x v` is available), with the count of the output of `V`. -/
def domLoops (s : ℕ) (PX : Xp) (V body : Gn) : Gn :=
  .loop (const (s + 1)) (.loopX PX (.count V body))

/-- Emit the coordinate number `i 2^ℓ + v` if the count is zero (loops entered at depth `D`). -/
def domBody (D : ℕ) : Gn :=
  when (Xp.eq (var (D + 5)) (const 0)) (.emit (add (shl (var (D + 1)) gℓ) (var (D + 3))))

/-- The description of the domain of the schema of a schema stack (record at `b + 28 …`),
run at depth `D`. -/
def domGen (s b D : ℕ) : Gn :=
  .count (domLoops s gP (violAt s b (D + 1)) (domBody (D + 1)))
    (.seq (.emit (var D)) (domLoops s gP (violAt s b (D + 1)) (domBody (D + 1))))

/-- The description of the permutation keeping the blocks with the shifts of the mask `mX`,
run at depth `D`. -/
def permGen (s : ℕ) (mX : Xp) (D : ℕ) : Gn :=
  .seq (.loop (const (s + 1)) (.emit (var (D + 1))))
    (.loop (const (s + 1)) (.emit (shiftX s mX (var (D + 1)))))

/-- The description of the schema of a schema stack (depth `b + 37`). -/
def schBody (s b : ℕ) : Gn :=
  .ite (Xp.eq (var (b + 28)) (const 1))
    (seqL [.emit (const 3), .emit (var (b + 29)), .emit (var (b + 30)), .emit (var (b + 31)),
      domGen s b (b + 37), permGen s (var (b + 32)) (b + 37), permGen s (const 0) (b + 37),
      permGen s (const 0) (b + 37)])
    (seqL [.emit (const 2), .emit (var (b + 29)), .emit (var (b + 30)),
      domGen s b (b + 37), permGen s (var (b + 32)) (b + 37), permGen s (const 0) (b + 37)])

/-- The initialization number of location `v`: `1` at `accept`, `2` at the detector output. -/
def initX (vX : Xp) : Xp := add (Xp.eq vX gacc) (mulC 2 (Xp.eq vX gdet))

/-- The locations (run at depth `b`). -/
def locGen (s b : ℕ) : Gn :=
  .loop gW (seqL [.emit (initX (var (b + 1))), .emit (mulC (s + 1) gP),
    .loop (mulC (s + 1) gP) (.emit (var (b + 3)))])

/-- **The generator of the system description** (run on the globals). -/
def sysGen (M : Machine) (s : ℕ) : Gn :=
  seqL [.emit (const (s + 1)), .emit gℓ, .emit gW, locGen s 14, .emit gE,
    schEnum M s 14 gH gR gN gr gp0 gEc (schBody s 14)]

end Gn

variable {M : Machine} {x : List Bool} {s ℓ H : ℕ}

/-! ## Domains -/

lemma out_domLoops {τ : List ℕ} {PX : Xp} (hPb : PX.Bnd τ.length) (hP : PX.eval τ = 2 ^ ℓ)
    (V body : Gn) :
    (Gn.domLoops s PX V body).out x τ =
      (List.range (s + 1)).flatMap fun i => (List.range (2 ^ ℓ)).flatMap fun v =>
        body.out x (τ ++ [s + 1, i, 2 ^ ℓ, v, inBit x v,
          (V.out x (τ ++ [s + 1, i, 2 ^ ℓ, v, inBit x v, 0])).length]) := by
  have key : ∀ l, PX.eval (τ ++ l) = 2 ^ ℓ := fun l => by rw [eval_append rfl l hPb, hP]
  simp only [Gn.domLoops, Gn.out, eval_const, key, List.append_assoc, List.cons_append,
    List.nil_append]

lemma out_domBody {σ : List ℕ} {D : ℕ} (hσ : σ.length = D) (hG : GlobOK M x s ℓ H σ)
    (i v c : ℕ) :
    (Gn.domBody D).out x (σ ++ [s + 1, i, 2 ^ ℓ, v, inBit x v, c]) =
      if c = 0 then [i * 2 ^ ℓ + v] else [] := by
  have hG' := hG.append [s + 1, i, 2 ^ ℓ, v, inBit x v, c]
  subst hσ
  rw [Gn.domBody, Gn.out_when, eval_eq_const]
  have e5 : (var (σ.length + 5)).eval (σ ++ [s + 1, i, 2 ^ ℓ, v, inBit x v, c]) = c := by
    rw [eval_var, getD_app]; rfl
  have e1 : (var (σ.length + 1)).eval (σ ++ [s + 1, i, 2 ^ ℓ, v, inBit x v, c]) = i := by
    rw [eval_var, getD_app]; rfl
  have e3 : (var (σ.length + 3)).eval (σ ++ [s + 1, i, 2 ^ ℓ, v, inBit x v, c]) = v := by
    rw [eval_var, getD_app]; rfl
  rw [e5]
  by_cases hc : c = 0
  · subst hc
    simp only [if_true, ne_eq, one_ne_zero, not_false_eq_true]
    simp only [Gn.out, eval_add, eval_shl, e1, e3, hG'.eℓ]
  · simp [hc]

open Classical in
/-- Membership of `(i, toBlk v)` in the domain of a schema. -/
noncomputable def memB {N : ℕ} (sc : Schema (s + 1) ℓ N) (i v : ℕ) : Bool :=
  if h : i < s + 1 then decide (((⟨i, h⟩, toBlk ℓ v) : Coord (s + 1) ℓ) ∈ sc.domain) else false

lemma memB_iff {N : ℕ} (sc : Schema (s + 1) ℓ N) {i : ℕ} (hi : i < s + 1) (v : ℕ) :
    memB sc i v = true ↔ ((⟨i, hi⟩, toBlk ℓ v) : Coord (s + 1) ℓ) ∈ sc.domain := by
  classical
  simp [memB, hi]

lemma out_domPass {ρ τ τ' : List ℕ} {b D e : ℕ}
    {sc : Schema (s + 1) ℓ (Iv M x s ℓ H).numLocations}
    (hG : GlobOK M x s ℓ H ρ) (hρ : ρ.length = b) (hctx : SchCtx M x s ℓ H b ρ τ e sc)
    (hτ' : τ'.take (b + 37) = τ) (hD : τ'.length = D) (hbD : b + 37 ≤ D) (hℓ : 0 < ℓ) :
    (Gn.domLoops s gP (violAt s b D) (Gn.domBody D)).out x τ' = domL (s + 1) ℓ (memB sc) := by
  have hb := hρ ▸ hG.le
  have hGτ : GlobOK M x s ℓ H τ := hG.of_take hρ hctx.2.1
  have hGτ' : GlobOK M x s ℓ H τ' := hGτ.of_take hctx.1 hτ'
  rw [out_domLoops (bnd_glob (by omega) (by rw [hD]; omega)) hGτ'.eP]
  unfold domL
  refine List.flatMap_congr fun i hi => List.flatMap_congr fun v hv => ?_
  rw [List.mem_range] at hi hv
  rw [out_domBody hD hGτ']
  have hviol := violAt_nil_iff hG hρ hctx hτ' hD hbD hℓ hi hv
  rw [← memB_iff sc hi v] at hviol
  by_cases hm : memB sc i v = true
  · rw [if_pos (List.length_eq_zero_iff.mpr (hviol.mpr hm)), if_pos hm]
  · rw [if_neg (fun h => hm (hviol.mp (List.length_eq_zero_iff.mp h))), if_neg hm]

lemma out_domGen {ρ τ τ' : List ℕ} {b D e : ℕ}
    {sc : Schema (s + 1) ℓ (Iv M x s ℓ H).numLocations}
    (hG : GlobOK M x s ℓ H ρ) (hρ : ρ.length = b) (hctx : SchCtx M x s ℓ H b ρ τ e sc)
    (hτ' : τ'.take (b + 37) = τ) (hD : τ'.length = D) (hbD : b + 37 ≤ D) (hℓ : 0 < ℓ) :
    (Gn.domGen s b D).out x τ' =
      (domL (s + 1) ℓ (memB sc)).length :: domL (s + 1) ℓ (memB sc) := by
  have ht : ∀ c, (τ' ++ [c]).take (b + 37) = τ := fun c => by
    rw [List.take_append_of_le_length (by omega), hτ']
  have hl : ∀ c, (τ' ++ [c]).length = D + 1 := fun c => by simp [hD]
  simp only [Gn.domGen, Gn.out]
  rw [out_domPass hG hρ hctx (ht 0) (hl 0) (by omega) hℓ,
    out_domPass hG hρ hctx (ht _) (hl _) (by omega) hℓ]
  simp only [eval_var, List.singleton_append]
  rw [← hD, List.getD_append_right _ _ _ _ le_rfl]
  simp

/-! ## Permutations -/

lemma out_permGen {σ : List ℕ} {D : ℕ} (hσ : σ.length = D) (hG : GlobOK M x s ℓ H σ) (mX : Xp)
    (hm : mX.Bnd D) :
    (Gn.permGen s mX D).out x σ =
      List.range (s + 1) ++ (List.range (s + 1)).map (shiftVal s ℓ (mX.eval σ)) := by
  simp only [Gn.permGen, Gn.out, eval_const]
  congr 1
  · rw [← List.map_eq_flatMap]
    · conv_rhs => rw [← List.map_id (List.range (s + 1))]
      refine List.map_congr_left fun k _ => ?_
      rw [eval_var, ← hσ, getD_app]; rfl
  · rw [← List.map_eq_flatMap]
    refine List.map_congr_left fun k _ => ?_
    rw [eval_shiftX (hG.append [s + 1, k]), eval_append hσ _ hm, eval_var, ← hσ, getD_app]
    rfl

/-! ## Schemas -/

/-- **The description of a schema.** -/
theorem out_schBody {ρ τ : List ℕ} {b e : ℕ} {sc : Schema (s + 1) ℓ (Iv M x s ℓ H).numLocations}
    (hG : GlobOK M x s ℓ H ρ) (hρ : ρ.length = b) (hctx : SchCtx M x s ℓ H b ρ τ e sc)
    (hℓ : 0 < ℓ) :
    (Gn.schBody s b).out x τ = schemaDescription sc := by
  have hb := hρ ▸ hG.le
  have hGτ : GlobOK M x s ℓ H τ := hG.of_take hρ hctx.2.1
  obtain ⟨g, -, hm⟩ := hctx.2.2.2
  simp only [getD_drop'] at hm
  rw [schemaDescription_of_match hm (memB sc) (fun i hi v _ => memB_iff sc hi v)]
  have hdom := out_domGen hG hρ hctx (List.take_of_length_le (by rw [hctx.1])) hctx.1 le_rfl hℓ
  have hp0 := out_permGen hctx.1 hGτ (const 0) trivial
  have hpm := out_permGen hctx.1 hGτ (var (b + 32)) (show b + 32 < b + 37 by omega)
  simp only [eval_const, eval_var] at hp0 hpm
  simp only [Gn.schBody, Gn.out, eval_eq_const, eval_var, Gn.out_seqL, List.flatMap_cons,
    List.flatMap_nil, eval_const]
  unfold schDescN
  by_cases ht : τ.getD (b + 28) 0 = 1
  · simp only [ht, if_true, ne_eq, one_ne_zero, not_false_eq_true, decide_true]
    rw [hdom, hpm, hp0]
    simp
  · simp only [ht, if_false, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true]
    rw [hdom, hpm, hp0]
    simp

/-! ## Locations -/

lemma out_locGen {ρ : List ℕ} {b : ℕ} (hρ : ρ.length = b) (hG : GlobOK M x s ℓ H ρ) :
    (Gn.locGen s b).out x ρ =
      (List.range (Iv M x s ℓ H).numLocations).flatMap fun v =>
        ((if v = (Loc.code (Loc.accept : Loc M H)).val then 1 else 0) +
          2 * (if v = numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 3 then 1 else 0)) ::
          ((s + 1) * 2 ^ ℓ) :: List.range ((s + 1) * 2 ^ ℓ) := by
  simp only [Gn.locGen, Gn.out, hG.eW, Gn.out_seqL, List.flatMap_cons, List.flatMap_nil]
  refine List.flatMap_congr fun v _ => ?_
  have hG' := hG.append [(Iv M x s ℓ H).numLocations, v]
  have hv : (var (b + 1)).eval (ρ ++ [(Iv M x s ℓ H).numLocations, v]) = v := by
    rw [eval_var, ← hρ, getD_app]; rfl
  simp only [Gn.initX, eval_add, eval_mulC, eval_eq, hv, hG'.eacc, hG'.edet, hG'.eP,
    List.append_nil, List.cons_append, List.nil_append, List.cons.injEq, true_and]
  rw [← List.map_eq_flatMap]
  conv_rhs => rw [← List.map_id (List.range ((s + 1) * 2 ^ ℓ))]
  refine List.map_congr_left fun k _ => ?_
  rw [eval_var, show b + 3 = (ρ ++ [(Iv M x s ℓ H).numLocations, v]).length + 1 by simp [hρ],
    getD_app]
  rfl

/-- The location part of the description of `Iv`. -/
lemma locsDesc_Iv :
    (List.finRange (Iv M x s ℓ H).numLocations).flatMap
        (fun v => initNum ((Iv M x s ℓ H).init v) ::
          domainDescription ((Iv M x s ℓ H).domain v)) =
      (List.range (Iv M x s ℓ H).numLocations).flatMap fun v =>
        ((if v = (Loc.code (Loc.accept : Loc M H)).val then 1 else 0) +
          2 * (if v = numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 3 then 1 else 0)) ::
          ((s + 1) * 2 ^ ℓ) :: List.range ((s + 1) * 2 ^ ℓ) := by
  have h1 := locsDesc_compile (APv M x s ℓ H) (Loc.query : Loc M H).code (fun _ _ => 0)
  have hacc : ((APv M x s ℓ H).loc (.prog (APv M x s ℓ H).accept)).val =
      (Loc.code (Loc.accept : Loc M H)).val := by
    rw [loc_prog_val]; rfl
  have hc : (APv M x s ℓ H).commands.length = (verifierCmds' M x s ℓ H).length := by
    simp only [AP_commands]; exact List.length_map _
  have hdet : ((APv M x s ℓ H).loc (.det .out)).val =
      numLoc M H + 8 * (verifierCmds' M x s ℓ H).length + 3 := by
    rw [loc_det_val, hc]
    simp only [DetSlot.toFin]
    show numLoc M H + _ * 8 + 3 = _
    ring
  rw [hacc, hdet] at h1
  exact h1

/-! ## The system -/

lemma flatMap_eq_range_get {α β : Type} (l : List α) (f : α → List β) :
    l.flatMap f = (List.range l.length).flatMap fun e => (l[e]?).elim [] f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, ih, List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    simp

/-- **The generator emits the description of the system.** -/
theorem out_sysGen (hℓ : 0 < ℓ) :
    (Gn.sysGen M s).out x (globs M x s ℓ H) = systemDescription (Iv M x s ℓ H) := by
  have hG : GlobOK M x s ℓ H (globs M x s ℓ H) := by
    unfold GlobOK; exact List.take_of_length_le (by rw [length_globs])
  obtain ⟨T, hT, hctx⟩ := schEnum_ctx length_globs hG
  have hS : (Iv M x s ℓ H).schemas.flatMap schemaDescription =
      (List.range (Iv M x s ℓ H).schemas.length).flatMap fun e =>
        (Gn.schBody s 14).out x (T e) := by
    rw [flatMap_eq_range_get]
    refine List.flatMap_congr fun e he => ?_
    rw [List.mem_range] at he
    rw [List.getElem?_eq_getElem he, Option.elim_some, out_schBody hG length_globs (hctx e he) hℓ]
  simp only [Gn.sysGen, Gn.out_seqL, List.flatMap_cons, List.flatMap_nil, Gn.out, eval_const,
    hG.eℓ, hG.eW, hG.eE, List.append_nil]
  rw [out_locGen length_globs hG, hT, systemDescription, locsDesc_Iv, hS]
  simp

end Lax119563Proofs.Reduction
