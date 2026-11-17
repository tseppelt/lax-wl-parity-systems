import Lax119563Proofs.Reduction.DescGen

/-!
# Well-formedness of the generators (`WFX`, `NoX`)

`Gn.Cl P`: a predicate on generators closed under `skip, emit, seq, ite, bind, loop, log, count`.
Both `NoX` and `WFX` are closed. For closed predicates: `seqL, when, dispatch, bindL, bindSub,
firstL, brGen, emitN, blkGen, cmdEnum, schEnum` preserve `P`; `slotLoops` gives `WFX` from a
`NoX` test and body. **`wfx_descGen`**: the output generator is well formed.
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

lemma Cl.dispatch (v : Xp) (n : ℕ) {f : ℕ → Gn} (hf : ∀ i, P (f i)) : P (dispatch v n f) :=
  hP.seqL fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg
    exact hP.when _ (hf i)

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

lemma Cl.cmdEnum (M : Machine) (s b : ℕ) (HX RX : Xp) {body : Gn} (hb : P body) :
    P (cmdEnum M s b HX RX body) := by
  unfold Lax119563Proofs.Reduction.cmdEnum
  refine hP.loop _ (hP.loop _ (hP.loop _ (hP.loop _ (hP.loop _ ?_))))
  refine hP.bindSub _ _ _ (hP.bindSub _ _ _ (hP.bindSub _ _ _ (hP.bindSub _ _ _ ?_)))
  refine hP.bind _ (hP.seqL fun g hg => ?_)
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hg
  exact hP.firstL _ (fun K => hP.bind _ (hP.brGen _ _ hb _)) _

lemma Cl.schEnum (M : Machine) (s b : ℕ) (HX RX NX rX p0X EcX : Xp) {body : Gn}
    (hb : P body) : P (schEnum M s b HX RX NX rX p0X EcX body) := by
  unfold Lax119563Proofs.Reduction.schEnum cmdBody detGen
  refine hP.seq (hP.cmdEnum _ _ _ _ _ (hP.count (hP.cmdEnum _ _ _ _ _ (hP.when _ (hP.emit _)))
    (hP.count (hP.cmdEnum _ _ _ _ _ (hP.when _ (hP.ite _ (hP.emitN 9) (hP.emitN 4))))
      (hP.ite _ (hP.blkGen _ _ hb _) (hP.blkGen _ _ hb _))))) ?_
  exact hP.bindL (hP.blkGen _ _ hb _) _

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

lemma wfx_slotLoops (s : ℕ) (PX : Xp) {V body : Gn} (hV : NoX V) (hb : NoX body) :
    WFX (slotLoops s PX V body) :=
  ⟨⟨hV, hb⟩, wfx_of_noX (g := .count V (.loop (const 4) body)) ⟨hV, hb⟩⟩

lemma noX_violGen (s d : ℕ) (iX vX xbX gkX g1X g2X g3X ℓX HX : Xp) :
    NoX (violGen s d iX vX xbX gkX g1X g2X g3X ℓX HX) := by
  unfold violGen
  have e : NoX (.emit (const 0)) := trivial
  exact cl_noX.when _ (cl_noX.ite _ (cl_noX.loop _ (cl_noX.when _ e))
    (cl_noX.ite _ (cl_noX.when _ e) (cl_noX.ite _ (cl_noX.when _ e) (cl_noX.when _ e))))

lemma noX_violAt (s b d : ℕ) : NoX (violAt s b d) := noX_violGen ..

lemma noX_colBody (s : ℕ) (vX FX iX vX' : Xp) : NoX (colBody s vX FX iX vX') :=
  ⟨trivial, trivial⟩

lemma noX_stepLoops (s : ℕ) {g : Gn} (h : NoX g) : NoX (stepLoops s g) := h

lemma wfx_stepLoops (s : ℕ) {g : Gn} (h : WFX g) : WFX (stepLoops s g) := h

lemma wfx_colSch (M : Machine) (s b : ℕ) (off validX : Xp) : WFX (colSch M s b off validX) :=
  cl_wfx.schEnum _ _ _ _ _ _ _ _ _ (wfx_slotLoops _ _ (noX_violAt ..) (noX_colBody ..))

lemma wfx_colStep (M : Machine) (s b : ℕ) (off validX : Xp) : WFX (colStep M s b off validX) :=
  cl_wfx.schEnum _ _ _ _ _ _ _ _ _
    (wfx_stepLoops _ (wfx_slotLoops _ _ (noX_violAt ..) (noX_colBody ..)))

lemma wfx_colPass (M : Machine) (s b : ℕ) : WFX (colPass M s b) := by
  unfold colPass
  refine cl_wfx.seqL fun g hg => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact wfx_colStep ..
  · exact wfx_colSch ..
  · exact wfx_colSch ..
  · exact cl_wfx.loop _ (wfx_slotLoops s gP trivial (noX_colBody ..))
  · exact wfx_colSch ..
  · exact wfx_colStep ..
  · exact wfx_colStep ..

lemma noX_pairGen (uX nX : Xp) : NoX (pairGen uX nX) := ⟨trivial, trivial⟩

lemma noX_plainGen (s : ℕ) (uX labX FX iX vX : Xp) : NoX (plainGen s uX labX FX iX vX) :=
  noX_pairGen ..

lemma noX_coordGen (s ε : ℕ) (uX wX iX vX rX : Xp) : NoX (coordGen s ε uX wX iX vX rX) :=
  cl_noX.when _ (noX_pairGen ..)

lemma noX_prevGen (s D : ℕ) (σX iX vX : Xp) : NoX (prevGen s D σX iX vX) :=
  noX_stepLoops _ (cl_noX.count (noX_stepLoops _ (cl_noX.when _ (cl_noX.emit _)))
    (cl_noX.when _ (cl_noX.emit _)))

lemma noX_edgeJuncBody (s ε b : ℕ) : NoX (edgeJuncBody s ε b) := by
  unfold edgeJuncBody
  refine cl_noX.ite _ (cl_noX.seqL fun g hg => ?_) cl_noX.skip
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact noX_coordGen ..
  · exact noX_coordGen ..
  · exact noX_plainGen ..

lemma noX_edgeLinkBody (s ε b : ℕ) : NoX (edgeLinkBody s ε b) := by
  unfold edgeLinkBody
  exact cl_noX.ite _ (cl_noX.seq (noX_coordGen ..) (cl_noX.count (noX_prevGen ..)
    (cl_noX.bindSub _ _ _ (noX_plainGen ..)))) cl_noX.skip

lemma noX_edgeUpdBody (s ε b : ℕ) : NoX (edgeUpdBody s ε b) := by
  unfold edgeUpdBody
  exact cl_noX.ite _ (cl_noX.seq (cl_noX.count (noX_prevGen ..)
    (cl_noX.ite _ (cl_noX.ite _ (noX_plainGen ..) (noX_coordGen ..))
      (cl_noX.bindSub _ _ _ (noX_plainGen ..))))
    (cl_noX.seq (noX_plainGen ..) (noX_plainGen ..))) cl_noX.skip

lemma wfx_edgePass (M : Machine) (s ε b : ℕ) : WFX (edgePass M s ε b) := by
  unfold edgePass edgeUpd edgeJunc edgeLink schSlots stepSlots
  refine cl_wfx.seqL fun g hg => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact cl_wfx.schEnum _ _ _ _ _ _ _ _ _
      (wfx_stepLoops _ (wfx_slotLoops _ _ (noX_violAt ..) (noX_edgeUpdBody ..)))
  · exact cl_wfx.schEnum _ _ _ _ _ _ _ _ _ (wfx_slotLoops _ _ (noX_violAt ..) (noX_edgeJuncBody ..))
  · exact cl_wfx.schEnum _ _ _ _ _ _ _ _ _ (wfx_slotLoops _ _ (noX_violAt ..) (noX_edgeLinkBody ..))

/-- **The output generator is well formed.** -/
theorem wfx_descGen (M : Machine) (s ε b : ℕ) : WFX (descGen M s ε b) := by
  unfold descGen
  refine cl_wfx.seqL fun g hg => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact trivial
  · exact wfx_colPass ..
  · exact cl_wfx.count (wfx_edgePass ..) (cl_wfx.seq trivial (wfx_edgePass ..))

end Gn

end Lax119563Proofs.Reduction
