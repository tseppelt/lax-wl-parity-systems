import Lax119563Proofs.Reduction.PassBase

/-!
# Well-formedness of the generators (`WFX`, `NoX`)

`Gn.Cl P`: a predicate on generators closed under `skip, emit, seq, ite, bind, loop, log, count`.
Both `NoX` and `WFX` are closed. For closed predicates: `seqL, when, dispatch, bindL, bindSub,
firstL, brGen, emitN, blkGen, cmdEnum, schEnum` preserve `P`; the domain test `violAt` is
`NoX`.
-/

namespace Lax119563Proofs.Reduction

open Circuits Lax489179.TuringMachine Xp

namespace Gn

/-- Closure under the constructors other than `loopX` and `len`. -/
structure Cl (P : Gn → Prop) : Prop where
  skip : P .skip
  emit : ∀ e, P (.emit e)
  seq : ∀ {g h}, P g → P h → P (.seq g h)
  ite : ∀ c {g h}, P g → P h → P (.ite c g h)
  bind : ∀ e {g}, P g → P (.bind e g)
  loop : ∀ l {g}, P g → P (.loop l g)
  log : ∀ e {g}, P g → P (.log e g)
  count : ∀ {g h}, P g → P h → P (.count g h)

lemma cl_noX : Cl NoX :=
  ⟨trivial, fun _ => trivial, fun hg hh => ⟨hg, hh⟩, fun _ _ _ hg hh => ⟨hg, hh⟩,
    fun _ _ hg => hg, fun _ _ hg => hg, fun _ _ hg => hg, fun hg hh => ⟨hg, hh⟩⟩

lemma cl_wfx : Cl WFX :=
  ⟨trivial, fun _ => trivial, fun hg hh => ⟨hg, hh⟩, fun _ _ _ hg hh => ⟨hg, hh⟩,
    fun _ _ hg => hg, fun _ _ hg => hg, fun _ _ hg => hg, fun hg hh => ⟨hg, hh⟩⟩

variable {P : Gn → Prop} (hP : Cl P)
include hP

lemma Cl.seqL : ∀ {gs : List Gn}, (∀ g ∈ gs, P g) → P (seqL gs)
  | [], _ => hP.skip
  | g :: gs, h => hP.seq (h g (by simp)) (Cl.seqL fun g' hg' => h g' (by simp [hg']))

lemma Cl.when (c : Xp) {g : Gn} (hg : P g) : P (when c g) := hP.ite c hg hP.skip

lemma Cl.bindL {g : Gn} (hg : P g) : ∀ es : List Xp, P (bindL es g)
  | [] => hg
  | e :: es => hP.bind e (Cl.bindL hg es)

lemma Cl.bindSub (n : ℕ) (a b : Xp) {g : Gn} (hg : P g) : P (bindSub n a b g) :=
  hP.count (hP.loop _ (hP.when _ (hP.emit _))) hg

lemma Cl.firstL {α : Type} (c : α → Xp) {f : α → Gn} (hf : ∀ a, P (f a)) :
    ∀ l : List α, P (firstL c f l)
  | [] => hP.skip
  | a :: l => hP.ite _ (hf a) (Cl.firstL c hf l)

lemma Cl.brGen {M : Machine} {s : ℕ} (RX HX : Xp) {body : Gn} (hb : P body) :
    ∀ brs : List (Xp × List (SMv M s)), P (brGen RX HX body brs)
  | [] => hP.skip
  | (c, ms) :: rest => hP.ite c (hP.seqL fun g hg => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hg
      exact hP.bindL hb _) (Cl.brGen RX HX hb rest)

lemma Cl.emitN (n : ℕ) : P (emitN n) :=
  hP.seqL fun g hg => by
    rw [List.eq_of_mem_replicate hg]; exact hP.emit _

lemma Cl.blkGen (e0 : Xp) (gd : List Xp) {body : Gn} (hb : P body) (blk : List (List Xp)) :
    P (blkGen e0 gd body blk) :=
  hP.seqL fun g hg => by
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hg
    exact hP.bindL hb _

end Gn

namespace Gn

lemma wfx_of_noX {g : Gn} (h : NoX g) : WFX g := by
  induction g with
  | skip => trivial
  | emit _ => trivial
  | seq _ _ ig ih => exact ⟨ig h.1, ih h.2⟩
  | ite _ _ _ ig ih => exact ⟨ig h.1, ih h.2⟩
  | bind _ _ ig => exact ig h
  | loop _ _ ig => exact ig h
  | loopX _ _ _ => exact h.elim
  | len _ _ => exact h.elim
  | log _ _ ig => exact ig h
  | count _ _ ig ih => exact ⟨ig h.1, ih h.2⟩

end Gn

end Lax119563Proofs.Reduction
