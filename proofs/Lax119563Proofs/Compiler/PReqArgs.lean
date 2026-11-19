import Lax119563Proofs.Compiler.PReqArg

/-!
# Pass `P3`, request generation: the argument loop of a schema

`p3Args` runs `p3Arg` for the `A` arguments (locations `locs` on `qLs2`, permutation
descriptions in the input), pushing `argsReqs` (**`p3Args_good`**).
-/

open Lax119563.ImplicitParitySystems Lax119563.ImplicitSystemEncodings
open Lax119563.BinaryEncodings Lax119563Proofs.Reduction Lax119563Proofs.Matrix

namespace Lax119563Proofs.Compiler

open CStm

variable {k ℓ : ℕ}

/-- The requests of argument `p = ((u, π), a)`. -/
def argReqs (cs : List (Coord k ℓ)) (base : ℕ) (tern : Bool) (p : (ℕ × BlockPerm k ℓ) × ℕ) :
    List (List ℕ) :=
  colReqs p.1.1 p.1.2 cs (base + sqOff tern p.2 cs.length) (sqStr tern)

/-- The requests of the arguments. -/
def argsReqs (locs : List ℕ) (perms : List (BlockPerm k ℓ)) (cs : List (Coord k ℓ))
    (base : ℕ) (tern : Bool) (a : ℕ) : List (List ℕ) :=
  (((locs.zip perms).zipIdx).take a).flatMap (argReqs cs base tern)

/-- The argument loop. -/
def p3Args : CStm CR CQ := .seq (.set rAi (.const 0)) (.loop (.lt (rv rAi) (rv rA)) p3Arg)

lemma zipIdx_getElem_zip {locs : List ℕ} {perms : List (BlockPerm k ℓ)}
    (hl : locs.length = perms.length) {a : ℕ} (ha : a < locs.length) :
    ((locs.zip perms).zipIdx)[a]'(by simp; omega) = ((locs[a], perms[a]'(by omega)), a) := by
  simp [List.getElem_zipIdx]

lemma argsReqs_succ (locs : List ℕ) (perms : List (BlockPerm k ℓ)) (cs : List (Coord k ℓ))
    (base : ℕ) (tern : Bool) {a : ℕ} (hl : a < locs.length) (hp : a < perms.length) :
    argsReqs locs perms cs base tern (a + 1) = argsReqs locs perms cs base tern a ++
      colReqs locs[a] perms[a] cs (base + sqOff tern a cs.length) (sqStr tern) := by
  have ha : a < ((locs.zip perms).zipIdx).length := by simp; omega
  rw [argsReqs, argsReqs, List.take_add_one, List.getElem?_eq_getElem ha, Option.toList_some,
    List.flatMap_append]
  simp [argReqs, List.getElem_zipIdx]

lemma flatMap_perms_split (perms : List (BlockPerm k ℓ)) {a : ℕ} (ha : a < perms.length) :
    (perms.drop a).flatMap permDescription =
      permDescription perms[a] ++ (perms.drop (a + 1)).flatMap permDescription := by
  rw [List.drop_eq_getElem_cons ha, List.flatMap_cons]

lemma flatMap_take_succ (perms : List (BlockPerm k ℓ)) {a : ℕ} (ha : a < perms.length) :
    (perms.take (a + 1)).flatMap permDescription =
      (perms.take a).flatMap permDescription ++ permDescription perms[a] := by
  rw [List.take_add_one, List.getElem?_eq_getElem ha, Option.toList_some, List.flatMap_append]
  simp

lemma args_arith (N P A m : ℕ) (hN : 64 ≤ N) :
    1 * N + N + (600 * N * P + A * (600 * (m + 1) * N + ((1 + 1 + 1) * N + 1)) +
      ((1 + 1 + 1) * N + 1)) ≤ 600 * (P + A * (m + 2) + 1) * N := by
  have : A * (600 * (m + 1) * N + ((1 + 1 + 1) * N + 1)) ≤ A * (600 * (m + 2) * N) :=
    Nat.mul_le_mul_left _ (by nlinarith)
  nlinarith

set_option maxHeartbeats 8000000 in
/-- **The arguments of a schema.** -/
lemma p3Args_good {x : List Bool} {w : ℕ} (hw : 2 ≤ w) (st : NSt CR CQ) (hb : st.Bdd w)
    (hpx : st.pos ≤ x.length) (locs : List ℕ) (perms : List (BlockPerm k ℓ))
    (cs : List (Coord k ℓ)) (tern : Bool) (base : ℕ) (rest : List Bool) {A : ℕ}
    (hl : locs.length = A) (hp : perms.length = A)
    (hs : (cs.map fun c => (c.1 : ℕ)).Pairwise (· ≤ ·)) (hk : 1 ≤ k)
    (hx : x.drop st.pos = encodeNats (perms.flatMap permDescription) ++ rest)
    (hKw : k * ℓ + k + 1 < 2 ^ w) (hℓw : ℓ + 1 < 2 ^ w) (huw : ∀ u ∈ locs, u < 2 ^ w)
    (hnw : cs.length + 1 < 2 ^ w) (hAw : A + 1 < 2 ^ w)
    (hsw : ∀ a < A, base + sqOff tern a cs.length + cs.length * sqStr tern < 2 ^ w)
    (hbits : ∀ π ∈ perms, ∀ v ∈ permDescription π, (Nat.bits v).length < w)
    (hKk : st.env rKk = k) (hKL : st.env rKL = k * ℓ) (hL : st.env rL = ℓ)
    (hD : st.env rD = cs.length) (hTn : st.env rTn = if tern then 1 else 0)
    (hSB : st.env rSB = base) (hStr : st.env rStr = sqStr tern) (hrA : st.env rA = A)
    (hLs : st.stk qLs2 = locs) (hF : st.stk qF = []) (hF2 : st.stk qF2 = [])
    (hDl : st.stk qDl = []) (hDl2 : st.stk qDl2 = []) (hDom : st.stk qDom = [])
    (hDom2 : st.stk qDom2 = cs.flatMap cdesc) (hAux : st.stk qAux = []) :
    ∃ st', Good x w p3Args st st'
        (600 * ((encodeNats (perms.flatMap permDescription)).length +
          A * (cs.length * (ℓ + 1) + 2) + 1) * Ex.nodeCost w) ∧
      st'.stk qLs2 = [] ∧ st'.stk qF = [] ∧ st'.stk qF2 = [] ∧ st'.stk qDl = [] ∧
      st'.stk qDl2 = [] ∧ st'.stk qDom = [] ∧ st'.stk qDom2 = cs.flatMap cdesc ∧
      st'.stk qAux = [] ∧
      st'.stk qRec = (argsReqs locs perms cs base tern A).flatten.reverse ++ st.stk qRec ∧
      (∀ q, q ≠ qLs2 → q ≠ qF → q ≠ qF2 → q ≠ qDl → q ≠ qDl2 → q ≠ qDom → q ≠ qDom2 →
        q ≠ qAux → q ≠ qRec → q ≠ qJunk → st'.stk q = st.stk q) ∧
      st'.pos = st.pos + (encodeNats (perms.flatMap permDescription)).length ∧
      st'.out = st.out ∧ ∀ r, wReg r p3Args = false → st'.env r = st.env r := by
  have hU0 := Ex.unitCost_le_nodeCost w
  have hU' := unitCost_ge w
  set n := cs.length
  set P := (encodeNats (perms.flatMap permDescription)).length
  have hxl : st.pos + P ≤ x.length := by
    have := congrArg List.length hx
    simp only [List.length_drop, List.length_append] at this; omega
  have r0 := Good.set (x := x) (w := w) (r := rAi) (e := .const 0) (st := st)
    (by simp only [Ex.Fits]; omega)
  set s0 := st.set rAi ((Ex.const 0 : Ex CR).eval st.env)
  set Inv : NSt CR CQ → Prop := fun s => s.env rAi ≤ A ∧ s.env rA = A ∧ s.env rKk = k ∧
    s.env rKL = k * ℓ ∧ s.env rL = ℓ ∧ s.env rD = n ∧ s.env rTn = (if tern then 1 else 0) ∧
    s.env rSB = base ∧ s.env rStr = sqStr tern ∧
    s.stk qLs2 = locs.drop (s.env rAi) ∧ s.stk qF = [] ∧ s.stk qF2 = [] ∧ s.stk qDl = [] ∧
    s.stk qDl2 = [] ∧ s.stk qDom = [] ∧ s.stk qDom2 = cs.flatMap cdesc ∧ s.stk qAux = [] ∧
    s.stk qRec = (argsReqs locs perms cs base tern (s.env rAi)).flatten.reverse ++ st.stk qRec ∧
    (∀ q, q ≠ qLs2 → q ≠ qF → q ≠ qF2 → q ≠ qDl → q ≠ qDl2 → q ≠ qDom → q ≠ qDom2 →
      q ≠ qAux → q ≠ qRec → q ≠ qJunk → s.stk q = st.stk q) ∧
    s.pos = st.pos + (encodeNats ((perms.take (s.env rAi)).flatMap permDescription)).length ∧
    s.out = st.out ∧ s.Bdd w ∧ (∀ r, wReg r p3Args = false → s.env r = st.env r) with hInv
  have hloop := Good.loop_var (x := x) (w := w) (e := .lt (rv rAi) (rv rA)) (body := p3Arg)
    Inv (fun s => A - s.env rAi) (fun s => st.pos + P - s.pos) (600 * Ex.nodeCost w)
    (600 * (n * (ℓ + 1) + 1) * Ex.nodeCost w) (by
      intro s ⟨ha, hA', hk', hkl, hl', hd, htn, hsb, hstr, hls, hf, hf2, hdl, hdl2, hdom, hdom2,
        haux, hrec, hS, hps, ho, hbs, he⟩
      refine ⟨⟨by simp only [rv, Ex.Fits]; omega, by simp only [rv, Ex.Fits]; omega⟩, ?_⟩
      intro hcond
      have hlt : s.env rAi < A := by simpa [rv, Ex.eval, hA'] using hcond
      set a := s.env rAi with hadef
      have hal : a < locs.length := by omega
      have hap : a < perms.length := by omega
      have hPa : (encodeNats ((perms.take a).flatMap permDescription)).length +
          (encodeNats (permDescription perms[a])).length +
          (encodeNats ((perms.drop (a + 1)).flatMap permDescription)).length = P := by
        simp only [P]
        conv_rhs => rw [← List.take_append_drop a perms, List.flatMap_append,
          flatMap_perms_split perms hap]
        simp only [encodeNats_append, List.length_append]; ring
      have hxa : x.drop s.pos = encodeNats (permDescription perms[a]) ++
          (encodeNats ((perms.drop (a + 1)).flatMap permDescription) ++ rest) := by
        have e : perms.flatMap permDescription = (perms.take a).flatMap permDescription ++
            (permDescription perms[a] ++ (perms.drop (a + 1)).flatMap permDescription) := by
          rw [← flatMap_perms_split perms hap, ← List.flatMap_append, List.take_append_drop]
        rw [hps, ← List.drop_drop, hx, e, encodeNats_append, encodeNats_append, List.append_assoc,
          List.append_assoc, List.drop_left]
      have hpsx : s.pos ≤ x.length := by omega
      have hls' : s.stk qLs2 = locs[a] :: locs.drop (a + 1) := by
        rw [hls, List.drop_eq_getElem_cons hal]
      obtain ⟨s', r', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
        p3Arg_good (x := x) hw s hbs hpsx locs[a] (locs.drop (a + 1)) perms[a] cs tern a base
          _ hs hk hxa hKw hℓw (huw _ (List.getElem_mem hal)) hnw (by omega)
          (hsw a hlt) (hbits _ (List.getElem_mem hap)) hk' hkl hl' hd htn
          hadef.symm hsb hstr hls' hf hf2 hdl hdl2 hdom hdom2 haux
      have hbs' := (r'.bdd hw hbs hpsx).1
      refine ⟨s', r'.mono ?_, ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, hbs', ?_⟩, by omega, by omega⟩
      · rw [h12, hps]
        have : st.pos + P - (st.pos + (encodeNats ((perms.take a).flatMap permDescription)).length)
            - (st.pos + P - (st.pos + (encodeNats ((perms.take a).flatMap permDescription)).length
              + (encodeNats (permDescription perms[a])).length)) =
            (encodeNats (permDescription perms[a])).length := by omega
        rw [this]; nlinarith
      · rw [h14 _ (by decide), hA']
      · rw [h14 _ (by decide), hk']
      · rw [h14 _ (by decide), hkl]
      · rw [h14 _ (by decide), hl']
      · rw [h14 _ (by decide), hd]
      · rw [h14 _ (by decide), htn]
      · rw [h14 _ (by decide), hsb]
      · rw [h14 _ (by decide), hstr]
      · rw [h11, h1]
      · exact h2
      · exact h3
      · exact h4
      · exact h5
      · exact h6
      · exact h7
      · exact h8
      · rw [h9, h11, argsReqs_succ _ _ _ _ _ hal hap, hrec]; simp
      · intro q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10
        rw [h10 q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10, hS q n1 n2 n3 n4 n5 n6 n7 n8 n9 n10]
      · rw [h12, hps, h11, flatMap_take_succ perms hap, encodeNats_append, List.length_append]
        ring
      · rw [h13, ho]
      · intro r hr
        rw [h14 r (by simp only [p3Args, wReg, Bool.or_eq_false_iff] at hr; exact hr.2), he r hr])
    s0 ⟨by simp [s0, Ex.eval], by simp [s0, Function.update_of_ne (show rA ≠ rAi by decide), hrA],
      by simp [s0, Function.update_of_ne (show rKk ≠ rAi by decide), hKk],
      by simp [s0, Function.update_of_ne (show rKL ≠ rAi by decide), hKL],
      by simp [s0, Function.update_of_ne (show rL ≠ rAi by decide), hL],
      by simp [s0, Function.update_of_ne (show rD ≠ rAi by decide), hD],
      by simp [s0, Function.update_of_ne (show rTn ≠ rAi by decide), hTn],
      by simp [s0, Function.update_of_ne (show rSB ≠ rAi by decide), hSB],
      by simp [s0, Function.update_of_ne (show rStr ≠ rAi by decide), hStr],
      by simp [s0, Ex.eval, hLs], hF, hF2, hDl, hDl2, hDom, hDom2, hAux,
      by simp [s0, Ex.eval, argsReqs], fun _ _ _ _ _ _ _ _ _ _ _ => rfl,
      by simp [s0, Ex.eval, encodeNats], rfl, (r0.bdd hw hb hpx).1,
      fun r hr => by
        simp only [p3Args, wReg, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
        simp [s0, Function.update_of_ne (Ne.symm hr.1)]⟩
  obtain ⟨s', r', ⟨ha, hA', -, -, -, -, -, -, -, hls, hf, hf2, hdl, hdl2, hdom, hdom2, haux, hrec,
    hS, hps, ho, -, he⟩, hc⟩ := hloop
  have haA : s'.env rAi = A := by
    simp only [Ex.eval, rv, hA'] at hc; split_ifs at hc with h <;> omega
  refine ⟨s', (r0.seq r').mono ?_, by rw [hls, haA, ← hl]; simp, hf, hf2, hdl, hdl2, hdom,
    hdom2, haux, by rw [hrec, haA], hS, by rw [hps, haA, ← hp, List.take_length], ho, he⟩
  have h0 : A - s0.env rAi = A := by simp [s0, Ex.eval]
  have h1 : st.pos + P - s0.pos = P := by simp [s0]
  rw [h0, h1]; simp only [condCost, rv, Ex.size]
  exact le_trans (by nlinarith) (args_arith (Ex.nodeCost w) P A (n * (ℓ + 1)) (by omega))

end Lax119563Proofs.Compiler
