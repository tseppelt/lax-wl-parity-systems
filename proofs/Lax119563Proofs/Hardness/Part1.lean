import Lax119563.BinaryEncodings
import Lax119563.GameCharacterization
import Lax119563.MatrixCompiler
import Lax119563.PackedRepresentation
import Lax119563.PebbleGame
import Lax119563.WLProblems
import Lax119563Proofs.Hierarchy.Part1
import Lax119563Proofs.Machines.Part1
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Bits
import Mathlib.Logic.Equiv.Basic
import Mathlib.Order.Basic

/-! ### Formerly `Lax119563Proofs.Machines.ComposeComputes` -/

section Machines_ComposeComputes

/-!
# Composing two machines that compute functions

The composed machine of `Main.Compose` (simulate `R`, rewind tape `0`, simulate `D` on tape `0`)
also composes *computations*: if `R` computes `y` from `x` within `t₁` steps and `D` computes
`z` from `y` within `t₂` steps, the composed machine computes `z` from `x` within
`2 t₁ + t₂ + 3` steps (for `|x| ≥ 2`; **`compose_computesWithin`**). At the end of the
simulation of `D`, tape `0` of the composed machine is the embedded tape `0` of `D`, which is
the input layout of `z` in the alphabet of the composed machine.
-/

open Lax489179.TuringMachine (Machine Config Move Instruction step run Deterministic)
open Lax119563.DeterministicTime

namespace Lax119563Proofs.Main.Compose

open AMachine

variable {R D : Machine} {a₀ : Bool} {a₁ : Bool → Bool}

/-- `ComputesWithin` is monotone in the time bound. -/
lemma computesWithin_mono' {M : Machine} {x y : List Bool} {t t' : ℕ}
    (h : ComputesWithin M x y t) (ht : t ≤ t') : ComputesWithin M x y t' := by
  have e : runOn M x t' = runOn M x t := runOn_eq_of_le M x ht h.1
  unfold ComputesWithin HaltsWithin at *
  rw [e]; exact h

/-- **Composition of computations.** -/
theorem compose_computesWithin (R D : Machine) (a₀ : Bool) (a₁ : Bool → Bool)
    {x y z : List Bool} {t₁ t₂ : ℕ} (hx : 2 ≤ x.length)
    (hR : ComputesWithin R x y t₁) (hD : ComputesWithin D y z t₂) :
    ComputesWithin (comp R D a₀ a₁).toMachine x z (2 * t₁ + t₂ + 3) := by
  classical
  have hex : ∃ t, (runOn R x t).answer.isSome := ⟨t₁, hR.1⟩
  have hth : (runOn R x (Nat.find hex)).answer.isSome := Nat.find_spec hex
  have hth_le : Nat.find hex ≤ t₁ := Nat.find_min' hex hR.1
  have hbefore : ∀ t < Nat.find hex, (runOn R x t).answer = none := fun t ht => by
    have := Nat.find_min hex ht
    simpa using this
  obtain ⟨t', ht'⟩ : ∃ t', Nat.find hex = t' + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h0 => ?_
    rw [h0] at hth
    simp [runOn, Lax489179.TuringMachine.run, Lax489179.TuringMachine.init] at hth
  rw [ht'] at hth hth_le hbefore
  have hsim : ∀ t ≤ t', SimR ((comp R D a₀ a₁).run (2 + t) (AMachine.init x)) (runOn R x t) := by
    intro t
    induction t with
    | zero => intro _; exact simR_init x hx
    | succ t ih =>
      intro ht
      rw [← Nat.add_assoc, AMachine.run_succ, runOn_succ]
      exact simR_step_next (ih (by omega)) (hbefore t (by omega))
        (by rw [← runOn_succ]; exact hbefore (t + 1) (by omega))
  set d := runOn R x (t' + 1) with hd
  have hrew : Rew ((comp R D a₀ a₁).run (2 + t' + 1) (AMachine.init x))
      (fun z => embR R D (d.tape 0 z)) (d.head 0) := by
    rw [AMachine.run_succ, hd, runOn_succ]
    exact simR_step_halt (hsim t' le_rfl) (hbefore t' (by omega))
      (by rw [← runOn_succ]; exact hth)
  have htape : d.tape 0 = (Lax489179.TuringMachine.init R y).tape 0 := by
    rw [hd, ← runOn_eq_of_le R x hth_le hth]
    exact hR.2
  rw [htape, embR_init_eq_embD_init] at hrew
  have hp : (d.head 0).natAbs ≤ t₁ := (head_natAbs_le R x 0 _).trans hth_le
  have hrew0 := rew_run (a₀ := a₀) (a₁ := a₁) _ _ _ rfl hrew
  have hsimD := simD_run (a₀ := a₀) (a₁ := a₁) (simD_of_rew (a₀ := a₀) (a₁ := a₁) hrew0) t₂
  set T := 2 + t' + 1 + (d.head 0).natAbs + 1 + t₂ with hT
  have hrun : (comp R D a₀ a₁).run T (AMachine.init x) =
      (comp R D a₀ a₁).run t₂ ((comp R D a₀ a₁).step ((comp R D a₀ a₁).run (d.head 0).natAbs
        ((comp R D a₀ a₁).run (2 + t' + 1) (AMachine.init x)))) := by
    rw [hT, AMachine.run_add, AMachine.run_succ, AMachine.run_add]
  refine computesWithin_mono' (t := T) ⟨?_, ?_⟩ (by omega)
  · unfold HaltsWithin
    rw [AMachine.runOn_toMachine, hrun]
    have hans := hsimD.2.1
    change _ = (runOn D y t₂).answer at hans
    show ((comp R D a₀ a₁).run t₂ _).answer.isSome
    rw [hans]; exact hD.1
  · rw [AMachine.runOn_toMachine, hrun, AMachine.init_enc]
    have ht0 := (hsimD.2.2 0).2
    change _ = fun w => embD R D ((runOn D y t₂).tape 0 w) at ht0
    rw [hD.2, ← embR_init_eq_embD_init (R := R), ← init_tape_none_embR (R := R) (D := D)] at ht0
    show ((comp R D a₀ a₁).run t₂ _).tape ((eT (Tp R D)).symm 0) =
      (AMachine.init z : Cfg R D).tape ((eT (Tp R D)).symm 0)
    have h0 : (eT (Tp R D)).symm 0 = none := (eT_symm_eq_none_iff 0).mpr rfl
    rw [h0]
    exact ht0

end Lax119563Proofs.Main.Compose

end Machines_ComposeComputes

/-! ### Formerly `Lax119563Proofs.Hardness.Decoding` -/

section Hardness_Decoding

/-!
# Decoding WL instances

* `encodeNats` is injective (`encodeNats_injective`), and the description of a colored graph
  determines the graph and is self-delimiting (`graphDescription_append_inj`). Hence
  `encodeWLInstance k G H ∈ WLDistinguishing ↔ Distinguishes k G H`
  (`encodeWLInstance_mem_iff`).
* The leading number of an encoded instance is its dimension (`leadingNat_encodeWLInstance`).
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.BinaryEncodings
  Lax119563.WLProblems

namespace Lax119563Proofs.Hardness

/-! ## Numbers -/

/-- The code of a digit list. -/
def codeL (ds : List Bool) : List Bool := ds.flatMap (fun d => [true, d]) ++ [false]

lemma encodeNat_eq_codeL (m : ℕ) : encodeNat m = codeL (Nat.bits m) := rfl

lemma codeL_append_inj : ∀ {ds ds' : List Bool} {r r' : List Bool},
    codeL ds ++ r = codeL ds' ++ r' → ds = ds' ∧ r = r'
  | [], [], r, r', h => by simpa [codeL] using h
  | [], d' :: ds', r, r', h => by simp [codeL] at h
  | d :: ds, [], r, r', h => by simp [codeL] at h
  | d :: ds, d' :: ds', r, r', h => by
    simp only [codeL, List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc,
      List.cons.injEq, true_and] at h
    obtain ⟨rfl, h⟩ := h
    have := codeL_append_inj (ds := ds) (ds' := ds') (r := r) (r' := r')
      (by simpa [codeL] using h)
    exact ⟨by rw [this.1], this.2⟩

lemma encodeNat_append_inj {a b : ℕ} {r r' : List Bool}
    (h : encodeNat a ++ r = encodeNat b ++ r') : a = b ∧ r = r' := by
  rw [encodeNat_eq_codeL, encodeNat_eq_codeL] at h
  obtain ⟨h1, h2⟩ := codeL_append_inj h
  exact ⟨Machines.bits_injective h1, h2⟩

/-- **`encodeNats` is injective.** -/
theorem encodeNats_injective : Function.Injective encodeNats := by
  intro l
  induction l with
  | nil =>
    intro l' h
    cases l' with
    | nil => rfl
    | cons b l' => simp [encodeNats, encodeNat] at h
  | cons a l ih =>
    intro l' h
    cases l' with
    | nil => simp [encodeNats, encodeNat] at h
    | cons b l' =>
      simp only [encodeNats, List.flatMap_cons] at h
      obtain ⟨rfl, h2⟩ := encodeNat_append_inj h
      rw [ih h2]

/-- The leading number of a code. -/
lemma leadingNat_codeL (ds : List Bool) (r : List Bool) :
    leadingNat (codeL ds ++ r) = Machines.valBits ds := by
  induction ds with
  | nil => simp [codeL, leadingNat, Machines.valBits]
  | cons d ds ih =>
    simp only [codeL, List.flatMap_cons, List.cons_append, List.nil_append,
      List.append_assoc] at ih ⊢
    rw [leadingNat, ih, Machines.valBits]
    cases d <;> rfl

lemma leadingNat_encodeNat_append (m : ℕ) (r : List Bool) :
    leadingNat (encodeNat m ++ r) = m := by
  rw [encodeNat_eq_codeL, leadingNat_codeL, Machines.valBits_bits]

/-- **The leading number of an encoded instance is its dimension.** -/
theorem leadingNat_encodeWLInstance (k : ℕ) (G H : ColoredGraph) :
    leadingNat (encodeWLInstance k G H) = k := by
  rw [encodeWLInstance, wlWord, encodeNats, List.flatMap_cons]
  exact leadingNat_encodeNat_append k _

/-! ## Graphs -/

lemma mem_edgeList {G : ColoredGraph} {u v : Fin G.n} :
    ((u : ℕ), (v : ℕ)) ∈ edgeList G ↔ u < v ∧ G.graph.Adj u v := by
  classical
  unfold edgeList
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_map, Prod.mk.injEq]
  simp
  constructor
  · rintro ⟨a, ⟨b, hb, hv⟩, ha⟩
    rw [Fin.val_inj] at hv ha
    subst hv ha; exact hb
  · intro h; exact ⟨u, ⟨v, h, rfl⟩, rfl⟩

lemma flatMap_pair_inj : ∀ {l l' : List (ℕ × ℕ)},
    l.flatMap (fun e => [e.1, e.2]) = l'.flatMap (fun e => [e.1, e.2]) → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | (a, b) :: l, (a', b') :: l', h => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl, h⟩ := h
    rw [flatMap_pair_inj h]

lemma graph_eq_of {G G' : ColoredGraph} (hn : G.n = G'.n)
    (hc : (List.finRange G.n).map G.color = (List.finRange G'.n).map G'.color)
    (he : edgeList G = edgeList G') : G = G' := by
  obtain ⟨n, g, c⟩ := G
  obtain ⟨n', g', c'⟩ := G'
  simp only at hn
  subst hn
  simp only at hc
  have hcol : c = c' := by
    funext i
    have := congrArg (fun l => l[(i : ℕ)]?) hc
    simpa using this
  subst hcol
  have hadj : ∀ u v : Fin n, u < v → (g.Adj u v ↔ g'.Adj u v) := by
    intro u v huv
    have h1 := @mem_edgeList ⟨n, g, c⟩ u v
    have h2 := @mem_edgeList ⟨n, g', c⟩ u v
    rw [he] at h1
    simp only at h1 h2
    constructor
    · intro h; exact (h2.mp (h1.mpr ⟨huv, h⟩)).2
    · intro h; exact (h1.mp (h2.mpr ⟨huv, h⟩)).2
  have : g = g' := by
    ext u v
    rcases lt_trichotomy u v with h | rfl | h
    · exact hadj u v h
    · simp
    · rw [g.adj_comm, g'.adj_comm]; exact hadj v u h
  subst this
  rfl

/-- **Graph descriptions are self-delimiting and determine the graph.** -/
theorem graphDescription_append_inj {G G' : ColoredGraph} {r r' : List ℕ}
    (h : graphDescription G ++ r = graphDescription G' ++ r') : G = G' ∧ r = r' := by
  unfold graphDescription at h
  simp only [List.cons_append, List.append_assoc, List.cons.injEq] at h
  obtain ⟨hn, h⟩ := h
  obtain ⟨hc, h⟩ := List.append_inj h (by simp [hn])
  simp only [List.cons.injEq] at h
  obtain ⟨hm, h⟩ := h
  obtain ⟨he, hr⟩ := List.append_inj h (by simp [hm])
  exact ⟨graph_eq_of hn hc (flatMap_pair_inj he), hr⟩

/-- **Membership of encoded instances.** -/
theorem encodeWLInstance_mem_iff (k : ℕ) (G H : ColoredGraph) :
    encodeWLInstance k G H ∈ WLDistinguishing ↔ Distinguishes k G H := by
  constructor
  · rintro ⟨k', G', H', heq, hd⟩
    have hw := encodeNats_injective heq
    simp only [wlWord, List.cons.injEq] at hw
    obtain ⟨rfl, hw⟩ := hw
    obtain ⟨rfl, hw⟩ := graphDescription_append_inj hw
    obtain ⟨rfl, -⟩ := graphDescription_append_inj (r := []) (r' := []) (by simpa using hw)
    exact hd
  · intro hd
    exact ⟨k, G, H, rfl, hd⟩

/-! ## Fixed instances -/

end Lax119563Proofs.Hardness

end Hardness_Decoding

/-! ### Formerly `Lax119563Proofs.Hardness.ExpAsymptotics` -/

section Hardness_ExpAsymptotics

/-!
# Estimates for the exponential lower bound

* `pow_le_two_rpow_quarter`: `m^d ≤ (4d + 4)^d 2^{m/4}`;
* `eps_mul_rpow_le`: if `N ≤ B m^5`, then `ε N^{1/5} ≤ m / 4` for
  `ε = 1 / (4 (B + 1)^{1/5})`;
* `two_rpow_quarter_add_le`: `2^{(n + c)/4} ≤ 2^c 2^{n/4}`.
-/

namespace Lax119563Proofs.Hardness

/-- A polynomial is dominated by `2^{m/4}`. -/
theorem pow_le_two_rpow_quarter (m d : ℕ) :
    (m : ℝ) ^ d ≤ ((4 * d + 4 : ℕ) : ℝ) ^ d * (2 : ℝ) ^ ((m : ℝ) / 4) := by
  set D := d + 1 with hD
  set k := m / (4 * D) with hk
  have h2D : 0 < 4 * D := by omega
  have hm : m ≤ 4 * D * 2 ^ k := by
    have h1 : m < 4 * D * (k + 1) := by
      have := Nat.lt_mul_div_succ m h2D
      rw [hk]; linarith
    have h2 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
    calc m ≤ 4 * D * (k + 1) := h1.le
      _ ≤ 4 * D * 2 ^ k := Nat.mul_le_mul_left _ h2
  have hmd : m ^ d ≤ (4 * D) ^ d * 2 ^ (k * d) := by
    calc m ^ d ≤ (4 * D * 2 ^ k) ^ d := Nat.pow_le_pow_left hm d
      _ = (4 * D) ^ d * 2 ^ (k * d) := by rw [mul_pow, ← pow_mul]
  have hkd : ((k * d : ℕ) : ℝ) ≤ (m : ℝ) / 4 := by
    have : 4 * (k * d) ≤ m := by
      have h1 : k * (4 * D) ≤ m := Nat.div_mul_le_self m (4 * D)
      have h2 : k * d ≤ k * D := Nat.mul_le_mul_left _ (by omega)
      have h3 : k * (4 * D) = 4 * (k * D) := by ring
      omega
    rw [le_div_iff₀ (by norm_num)]
    exact_mod_cast (by omega : k * d * 4 ≤ m)
  have hpow : ((2 : ℝ) ^ (k * d : ℕ)) ≤ (2 : ℝ) ^ ((m : ℝ) / 4) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hkd
  have hcast : ((m ^ d : ℕ) : ℝ) ≤ (((4 * D) ^ d * 2 ^ (k * d) : ℕ) : ℝ) := by exact_mod_cast hmd
  push_cast at hcast
  have e : (4 * (D : ℝ)) = ((4 * d + 4 : ℕ) : ℝ) := by rw [hD]; push_cast; ring
  rw [e] at hcast
  calc (m : ℝ) ^ d ≤ ((4 * d + 4 : ℕ) : ℝ) ^ d * 2 ^ (k * d) := hcast
    _ ≤ ((4 * d + 4 : ℕ) : ℝ) ^ d * (2 : ℝ) ^ ((m : ℝ) / 4) := by gcongr

/-- The exponent estimate. -/
theorem eps_mul_rpow_le (B N m : ℕ) (h : N ≤ B * m ^ 5) :
    1 / (4 * ((B : ℝ) + 1) ^ ((1 : ℝ) / 5)) * (N : ℝ) ^ ((1 : ℝ) / 5) ≤ (m : ℝ) / 4 := by
  have hB : (0 : ℝ) < (B : ℝ) + 1 := by positivity
  have hBr : 0 < ((B : ℝ) + 1) ^ ((1 : ℝ) / 5) := Real.rpow_pos_of_pos hB _
  have hN : (N : ℝ) ≤ ((B : ℝ) + 1) * (m : ℝ) ^ 5 := by
    have : (N : ℝ) ≤ (B : ℝ) * (m : ℝ) ^ 5 := by exact_mod_cast h
    nlinarith [pow_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) 5]
  have h1 : (N : ℝ) ^ ((1 : ℝ) / 5) ≤ (((B : ℝ) + 1) * (m : ℝ) ^ 5) ^ ((1 : ℝ) / 5) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hN (by norm_num)
  have h2 : (((B : ℝ) + 1) * (m : ℝ) ^ 5) ^ ((1 : ℝ) / 5) =
      ((B : ℝ) + 1) ^ ((1 : ℝ) / 5) * (m : ℝ) := by
    rw [Real.mul_rpow hB.le (by positivity)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  rw [h2] at h1
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- Shifting the exponent. -/
theorem two_rpow_quarter_add_le (n c : ℕ) :
    (2 : ℝ) ^ (((n + c : ℕ) : ℝ) / 4) ≤ (2 ^ c : ℕ) * (2 : ℝ) ^ ((n : ℝ) / 4) := by
  have e : (((n + c : ℕ) : ℝ) / 4) = (n : ℝ) / 4 + (c : ℝ) / 4 := by push_cast; ring
  rw [e, Real.rpow_add (by norm_num), mul_comm]
  gcongr
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [(Nat.cast_nonneg c : (0 : ℝ) ≤ c)])

end Lax119563Proofs.Hardness

end Hardness_ExpAsymptotics

/-! ### Formerly `Lax119563Proofs.Hardness.SimMachine` -/

section Hardness_SimMachine

/-!
# Simulating a machine of the model inside a structured machine

For a deterministic machine `D` of the model, `simTM D` is a structured machine
(`Machines.TM`) on the tapes of `D` plus a marker tape. It simulates `D` step by step; the head
of the marker tape (which holds a single mark at the origin) moves together with the head of
tape `0`, and the control state remembers on which side of the origin that head is. When `D`
halts, the head of tape `0` is moved back to the origin. So if `D` computes `z` from `y`
within `t` steps, `simTM D` ends within `2 t` transitions with `z` on tape `0` as a word tape
with the head on position `0` (`simTM_runsWithin`).

The length of an output is bounded by the length of the input plus the running time
(`length_le_of_computesWithin`).
-/

open Lax489179.TuringMachine (Machine Config Move Instruction init step run Deterministic)
open Lax119563.DeterministicTime

namespace Lax119563Proofs.Hardness

open Machines

/-- The symbols of a machine with `m + 3` symbols as a tape alphabet: blank `0`, bits `1, 2`. -/
instance finAlphabet (m : ℕ) : TapeAlphabet (Fin (m + 3)) where
  blank := 0
  bit b := if b then 2 else 1
  bit_injective := by
    intro a b h
    cases a <;> cases b <;> simp_all [Fin.ext_iff, Nat.mod_eq_of_lt (show 2 < m + 3 by omega),
      Nat.mod_eq_of_lt (show 1 < m + 3 by omega)]
  bit_ne_blank := by
    intro b
    cases b <;> simp [Fin.ext_iff, Nat.mod_eq_of_lt (show 2 < m + 3 by omega)]

lemma one_ne_zero_fin (m : ℕ) : (1 : Fin (m + 3)) ≠ 0 :=
  TapeAlphabet.bit_ne_blank (Γ := Fin (m + 3)) false

lemma two_ne_zero_fin (m : ℕ) : (2 : Fin (m + 3)) ≠ 0 :=
  TapeAlphabet.bit_ne_blank (Γ := Fin (m + 3)) true

/-! ## Output length -/

theorem tape_zero_blank (M : Machine) (x : List Bool) (t : ℕ) (z : ℤ)
    (hz : (x.length : ℤ) + t ≤ z) : (runOn M x t).tape 0 z = 0 := by
  induction t generalizing z with
  | zero =>
    simp only [runOn, run, init]
    have : x[z.toNat]? = none := List.getElem?_eq_none (by omega)
    simp [this]
  | succ t ih =>
    rw [Main.runOn_succ]
    have hh := Main.Compose.head_natAbs_le M x 0 t
    unfold step
    rcases (runOn M x t).answer with _ | b
    · dsimp only
      split
      · exact ih z (by omega)
      · dsimp only
        rw [if_neg (by omega)]
        exact ih z (by omega)
    · exact ih z (by omega)

/-- **The output is not longer than the input plus the running time.** -/
theorem length_le_of_computesWithin {M : Machine} {x y : List Bool} {t : ℕ}
    (h : ComputesWithin M x y t) : y.length ≤ x.length + t := by
  by_contra hlt
  push Not at hlt
  have h0 := tape_zero_blank M x t ((x.length + t : ℕ) : ℤ) (by push_cast; omega)
  rw [h.2] at h0
  simp only [init, Int.toNat_natCast, List.getElem?_eq_getElem hlt] at h0
  rw [if_pos ⟨trivial, by omega⟩] at h0
  revert h0
  cases y[x.length + t]
  · exact one_ne_zero_fin _
  · exact two_ne_zero_fin _

/-! ## The simulating machine -/

variable (D : Machine)

/-- The marker tape. -/
def mkI : Fin (D.tapes + 2) := Fin.last (D.tapes + 1)

/-- The mark at the origin. -/
def mark : Fin (D.symbols + 3) := bit false

/-- The cells of the marker tape. -/
def markCells : ℤ → Fin (D.symbols + 3) := listCells [mark D]

lemma markCells_eq_mark_iff (z : ℤ) : markCells D z = mark D ↔ z = 0 := by
  unfold markCells listCells
  constructor
  · intro h
    by_contra hz
    split_ifs at h with h0
    · have : [mark D][z.toNat]? = none := List.getElem?_eq_none (by simp; omega)
      rw [this] at h
      exact (TapeAlphabet.bit_ne_blank (Γ := Fin (D.symbols + 3)) false) h.symm
    · exact (TapeAlphabet.bit_ne_blank (Γ := Fin (D.symbols + 3)) false) h.symm
  · rintro rfl; simp

/-- Whether a move goes right. -/
def isRight : Move → Bool
  | .right => true
  | _ => false

/-- The direction of the rewinding moves. -/
def dir (sg : Bool) : Move := if sg then .left else .right

lemma castSucc_ne_mkI (j : Fin (D.tapes + 1)) : j.castSucc ≠ mkI D :=
  Fin.castSucc_ne_last j

lemma zero_ne_mkI : (0 : Fin (D.tapes + 2)) ≠ mkI D := by
  simpa using castSucc_ne_mkI D 0

/-- The simulating machine. States `inl (q, sg)` simulate `D` in state `q`, with `sg` the
side of the origin of the head of tape `0` (`true`: right); states `inr sg` rewind. -/
def simTM : TM (D.tapes + 2) (Fin (D.symbols + 3)) where
  Q := (Fin (D.states + 1) × Bool) ⊕ Bool
  start := .inl (0, true)
  δ
    | .inl (q, sg), s =>
      match D.transition q (fun j => s j.castSucc) false with
      | .halt _ => some (.inr sg, s, fun _ => .stay)
      | .next q' w m =>
        some (.inl (q', if s (mkI D) = mark D then isRight (m 0) else sg),
          Fin.lastCases (motive := fun _ => Fin (D.symbols + 3)) (s (mkI D)) w,
          Fin.lastCases (motive := fun _ => Move) (m 0) m)
    | .inr sg, s =>
      if s (mkI D) = mark D then none
      else some (.inr sg, s, Fin.lastCases (motive := fun _ => Move) (dir sg)
        (fun j => if j = 0 then dir sg else .stay))

variable {D}

/-- The rewinding phase: the head of tape `0` and of the marker tape are on position `±d`
(the sign given by `sg`), and they move back to the origin in `d` transitions. -/
theorem rew_haltsFrom : ∀ (d : ℕ) (T : Machines.Tapes (D.tapes + 2) (Fin (D.symbols + 3)))
    (sg : Bool), T (mkI D) = ⟨(T 0).head, markCells D⟩ →
    ((T 0).head = d ∧ sg = true ∨ (T 0).head = -d ∧ sg = false) →
    (simTM D).HaltsFrom (.inr sg) T d
      (Function.update (Function.update T 0 ⟨0, (T 0).cells⟩) (mkI D) ⟨0, markCells D⟩) := by
  intro d
  induction d with
  | zero =>
    intro T sg hmk hsg
    have h0 : (T 0).head = 0 := by omega
    have hT : Function.update (Function.update T 0 ⟨0, (T 0).cells⟩) (mkI D)
        ⟨0, markCells D⟩ = T := by
      funext i
      by_cases hi : i = mkI D
      · subst hi; rw [Function.update_self, hmk, h0]
      · rw [Function.update_of_ne hi]
        by_cases hi0 : i = 0
        · subst hi0; rw [Function.update_self, ← h0]
        · rw [Function.update_of_ne hi0]
    rw [hT]
    refine .halt ?_
    have : readAll T (mkI D) = mark D := by
      simp only [readAll, Tape.read, hmk, h0, markCells_eq_mark_iff]
    simp [simTM, this]
  | succ d ih =>
    intro T sg hmk hsg
    have hne : (T 0).head ≠ 0 := by omega
    have hread : readAll T (mkI D) ≠ mark D := by
      simp only [readAll, Tape.read, hmk, ne_eq, markCells_eq_mark_iff]; exact hne
    set mv : Fin (D.tapes + 2) → Move := Fin.lastCases (motive := fun _ => Move) (dir sg)
        (fun j => if j = 0 then dir sg else .stay) with hmv
    have hδ : (simTM D).δ (.inr sg) (readAll T) = some (.inr sg, readAll T, mv) := by
      show (if readAll T (mkI D) = mark D then none else some _) = _
      rw [if_neg hread]
      rfl
    have hmv0 : mv 0 = dir sg := by
      have : (0 : Fin (D.tapes + 2)) = (0 : Fin (D.tapes + 1)).castSucc := rfl
      rw [this, hmv, Fin.lastCases_castSucc]; simp
    have hmvm : mv (mkI D) = dir sg := by rw [hmv, mkI, Fin.lastCases_last]
    have hmvo : ∀ i, i ≠ 0 → i ≠ mkI D → mv i = .stay := by
      intro i hi0 him
      induction i using Fin.lastCases with
      | last => exact absurd rfl him
      | cast j =>
        rw [hmv, Fin.lastCases_castSucc]
        have : j ≠ 0 := by rintro rfl; exact hi0 rfl
        simp [this]
    set T₁ := applyAll T (readAll T) mv with hT₁
    have hT₁i : ∀ i, T₁ i = (T i).move (mv i) := fun i => Tape.act_read _ _
    have hoff : (dir sg).offset = if sg then -1 else 1 := by
      cases sg <;> rfl
    have h₁0 : T₁ 0 = ⟨(T 0).head + (dir sg).offset, (T 0).cells⟩ := by
      rw [hT₁i, hmv0]; rfl
    have h₁m : T₁ (mkI D) = ⟨(T₁ 0).head, markCells D⟩ := by
      rw [hT₁i, hmvm, h₁0, hmk]; rfl
    have hsg₁ : (T₁ 0).head = d ∧ sg = true ∨ (T₁ 0).head = -d ∧ sg = false := by
      rw [h₁0]
      rcases hsg with ⟨h, rfl⟩ | ⟨h, rfl⟩
      · left; refine ⟨?_, rfl⟩
        show (T 0).head + -1 = (d : ℤ)
        push_cast at h; omega
      · right; refine ⟨?_, rfl⟩
        show (T 0).head + 1 = -(d : ℤ)
        push_cast at h; omega
    have := ih T₁ sg h₁m hsg₁
    have hfin : Function.update (Function.update T₁ 0 ⟨0, (T₁ 0).cells⟩) (mkI D)
        ⟨0, markCells D⟩ =
        Function.update (Function.update T 0 ⟨0, (T 0).cells⟩) (mkI D) ⟨0, markCells D⟩ := by
      funext i
      by_cases hi : i = mkI D
      · subst hi; simp
      · rw [Function.update_of_ne hi, Function.update_of_ne hi]
        by_cases hi0 : i = 0
        · subst hi0; simp [h₁0]
        · rw [Function.update_of_ne hi0, Function.update_of_ne hi0, hT₁i, hmvo i hi0 hi]
          simp [Tape.move]
    rw [hfin] at this
    rw [show d + 1 = d + 1 from rfl]
    exact .step hδ this

/-- The simulation invariant between a configuration of `D` and the tapes of `simTM D`. -/
structure Rel (c : Config D) (sg : Bool) (T : Machines.Tapes (D.tapes + 2) (Fin (D.symbols + 3))) :
    Prop where
  tapes : ∀ j : Fin (D.tapes + 1), T j.castSucc = ⟨c.head j, c.tape j⟩
  mkt : T (mkI D) = ⟨c.head 0, markCells D⟩
  pos : 0 < c.head 0 → sg = true
  neg : c.head 0 < 0 → sg = false

lemma Rel.read {c : Config D} {sg : Bool} {T : Machines.Tapes (D.tapes + 2) (Fin (D.symbols + 3))}
    (h : Rel c sg T) : (fun j : Fin (D.tapes + 1) => readAll T j.castSucc) =
      fun j => c.tape j (c.head j) := by
  funext j; simp [readAll, Tape.read, h.tapes j]

lemma Rel.tape0 {c : Config D} {sg : Bool} {T : Machines.Tapes (D.tapes + 2) (Fin (D.symbols + 3))}
    (h : Rel c sg T) : T 0 = ⟨c.head 0, c.tape 0⟩ := h.tapes 0

theorem sim_haltsFrom : ∀ (t : ℕ) (c : Config D) (sg : Bool)
    (T : Machines.Tapes (D.tapes + 2) (Fin (D.symbols + 3))),
    c.answer = none → Rel c sg T → (run D t (fun _ => false) c).answer.isSome →
    ∃ t' ≤ t + ((run D t (fun _ => false) c).head 0).natAbs, ∃ T',
      (simTM D).HaltsFrom (.inl (c.state, sg)) T t' T' ∧
        T' 0 = ⟨0, (run D t (fun _ => false) c).tape 0⟩ := by
  intro t
  induction t with
  | zero => intro c sg T hc _ h; simp [run, hc] at h
  | succ t ih =>
    intro c sg T hc hR h
    rw [TM.run_succ_false] at h ⊢
    have hread := hR.read
    rcases htr : D.transition c.state (fun j => c.tape j (c.head j)) false with b | ⟨q', w, m⟩
    · -- `D` halts: rewind
      have hs : step D false c = { c with answer := some b } := by simp [step, hc, htr]
      rw [hs, Main.run_false_of_halted _ _ _ (by simp)]
      have hδ : (simTM D).δ (.inl (c.state, sg)) (readAll T) =
          some (.inr sg, readAll T, fun _ => .stay) := by
        simp only [simTM]; rw [hread, htr]
      have hT0 := hR.tape0
      have hrew := rew_haltsFrom (c.head 0).natAbs T sg (by rw [hR.mkt, hT0])
        (by
          rw [hT0]
          dsimp only
          rcases lt_trichotomy (c.head 0) 0 with hl | hl | hl
          · right; exact ⟨by omega, hR.neg hl⟩
          · cases sg
            · right; exact ⟨by omega, rfl⟩
            · left; exact ⟨by omega, rfl⟩
          · left; exact ⟨by omega, hR.pos hl⟩)
      refine ⟨(c.head 0).natAbs + 1, by simp,
        Function.update (Function.update T 0 ⟨0, (T 0).cells⟩) (mkI D) ⟨0, markCells D⟩,
        .step hδ (by simpa using hrew), ?_⟩
      rw [Function.update_of_ne (zero_ne_mkI D), Function.update_self, hT0]
    · have hs : step D false c = ⟨q', fun j => c.head j + (m j).offset,
          fun j z => if z = c.head j then w j else c.tape j z, none⟩ := by
        simp [step, hc, htr]
      rw [hs] at h ⊢
      set sg' := if readAll T (mkI D) = mark D then isRight (m 0) else sg with hsg'
      set W := Fin.lastCases (motive := fun _ => Fin (D.symbols + 3)) (readAll T (mkI D)) w
      set Mv := Fin.lastCases (motive := fun _ => Move) (m 0) m
      have hδ : (simTM D).δ (.inl (c.state, sg)) (readAll T) = some (.inl (q', sg'), W, Mv) := by
        simp only [simTM]; rw [hread, htr]
      have hR' : Rel ⟨q', fun j => c.head j + (m j).offset,
          fun j z => if z = c.head j then w j else c.tape j z, none⟩ sg' (applyAll T W Mv) := by
        have hmkread : readAll T (mkI D) = markCells D (c.head 0) := by
          simp [readAll, Tape.read, hR.mkt]
        refine ⟨fun j => ?_, ?_, ?_, ?_⟩
        · simp only [applyAll, W, Mv, Fin.lastCases_castSucc, hR.tapes j, Tape.act]
          congr 1
          funext z; simp [Function.update_apply]
        · simp only [applyAll, W, Mv, mkI, Fin.lastCases_last]
          rw [show Fin.last (D.tapes + 1) = mkI D from rfl, hR.mkt]
          simp only [Tape.act, Tape.mk.injEq, true_and]
          funext z
          rw [Function.update_apply]
          split_ifs with hz
          · subst hz; simp [readAll, Tape.read, hR.mkt]
          · rfl
        · intro hpos
          dsimp only at hpos
          simp only [hsg', hmkread, markCells_eq_mark_iff]
          split_ifs with h0
          · have := Main.Compose.offset_bound (m 0)
            rcases hm : m 0 <;> simp_all [Move.offset, isRight]
          · exact hR.pos (by have := Main.Compose.offset_bound (m 0); omega)
        · intro hneg
          dsimp only at hneg
          simp only [hsg', hmkread, markCells_eq_mark_iff]
          split_ifs with h0
          · have := Main.Compose.offset_bound (m 0)
            rcases hm : m 0 <;> simp_all [Move.offset, isRight]
          · exact hR.neg (by have := Main.Compose.offset_bound (m 0); omega)
      obtain ⟨t', ht', T', hH, hT'⟩ := ih _ sg' _ rfl hR' h
      exact ⟨t' + 1, by omega, T', .step hδ hH, hT'⟩

end Lax119563Proofs.Hardness

end Hardness_SimMachine

/-! ### Formerly `Lax119563Proofs.Hardness.LeadMachine` -/

section Hardness_LeadMachine

/-!
# Keeping the leading number of the input

For a deterministic machine `D`, the machine `(withLead D).compile` copies the leading number
code `encodeNat m` of its input to a separate tape, runs `D` on the whole input (by `simTM`),
and then writes `encodeNat m` in front of the output of `D`. So if `D` computes `z` from
`encodeNat m ++ v` within `t` steps, it computes `encodeNat m ++ z` within
`16 (t + |encodeNat m ++ v| + 1)` steps (`withLead_computesWithin`).
-/

open Lax489179.TuringMachine (Machine Config Move Instruction init step run Deterministic)
open Lax119563.DeterministicTime Lax119563.BinaryEncodings

namespace Lax119563Proofs.Hardness

open Machines Machines.TM Function

section CopyLead

variable {Γ : Type} [TapeAlphabet Γ] {k : ℕ}

/-- Copy one symbol from tape `i` to tape `j`, moving both heads right. -/
def cp (i j : Fin k) : TM k Γ := act₂ i j fun a _ => ((a, .right), (a, .right))

/-- Copy the leading number code from tape `i` to tape `j`. -/
def copyLead [DecidableEq Γ] (i j : Fin k) : TM k Γ :=
  loop (fun s => decide (s i = bit true)) (cp i j ;; cp i j) ;; cp i j

/-- The pairs `true, d` of a number code. -/
def pairs (ds : List Bool) : List Bool := ds.flatMap fun d => [true, d]

lemma cp_ofWord {i j : Fin k} (hij : i ≠ j) {T : Tapes k Γ} {pre rest dpre : List Γ} (a : Γ)
    (hTi : T i = .ofWord pre (a :: rest)) (hTj : T j = .ofWord dpre []) :
    (cp i j).RunsWithin T 1
      (update (update T i (.ofWord (pre ++ [a]) rest)) j (.ofWord (dpre ++ [a]) [])) := by
  have h₁ := act₂_runsWithin hij (fun a _ => ((a, Move.right), (a, Move.right))) T
  simp only [hTi, hTj, Tape.read_ofWord_cons, Tape.act_ofWord_right, List.tail_cons,
    List.tail_nil] at h₁
  exact h₁

theorem copyLoop_ofWord [DecidableEq Γ] {i j : Fin k} (hij : i ≠ j) (ds : List Bool) :
    ∀ {T : Tapes k Γ} {pre dpre r : List Γ},
    T i = .ofWord pre (bitsWord (pairs ds) ++ (bit false :: r)) → T j = .ofWord dpre [] →
    (loop (fun s => decide (s i = bit true)) (cp i j ;; cp i j)).RunsWithin T (3 * ds.length)
      (update (update T i (.ofWord (pre ++ bitsWord (pairs ds)) (bit false :: r))) j
        (.ofWord (dpre ++ bitsWord (pairs ds)) [])) := by
  induction ds with
  | nil =>
    intro T pre dpre r hTi hTj
    have hc : (fun s : Fin k → Γ => decide (s i = bit true)) (readAll T) = false := by
      simp [readAll, hTi, pairs, bitsWord]
    refine (loop_runsWithin_exit hc).congr_right ?_
    simp only [pairs, List.flatMap_nil, bitsWord, List.map_nil, List.append_nil,
      List.nil_append] at hTi ⊢
    rw [← hTi, ← hTj]; simp
  | cons d ds ih =>
    intro T pre dpre r hTi hTj
    have hTi' : T i = .ofWord pre (bit true :: bit d :: (bitsWord (pairs ds) ++ bit false :: r)) := by
      rw [hTi]; simp [pairs, bitsWord]
    have h₁ := cp_ofWord hij (bit true) hTi' hTj
    set T₁ := update (update T i (Tape.ofWord (pre ++ [bit true])
      (bit d :: (bitsWord (pairs ds) ++ bit false :: r)))) j (Tape.ofWord (dpre ++ [bit true]) [])
    have h₂ := cp_ofWord (T := T₁) (pre := pre ++ [bit true])
      (rest := bitsWord (pairs ds) ++ bit false :: r) (dpre := dpre ++ [bit true]) hij (bit d) (by simp [T₁, update_of_ne hij]) (by simp [T₁])
    have h₃ := ih (T := update (update T₁ i (Tape.ofWord (pre ++ [bit true] ++ [bit d])
        (bitsWord (pairs ds) ++ bit false :: r))) j (Tape.ofWord (dpre ++ [bit true] ++ [bit d]) []))
      (pre := pre ++ [bit true] ++ [bit d]) (dpre := dpre ++ [bit true] ++ [bit d]) (r := r)
      (by simp [update_of_ne hij]) (by simp)
    have hc : (fun s : Fin k → Γ => decide (s i = bit true)) (readAll T) = true := by
      simp [readAll, hTi']
    have h := loop_runsWithin_iter hc (seq_runsWithin h₁ h₂) h₃
    refine (h.mono (by simp; omega)).congr_right ?_
    simp only [T₁, update_update_update_update hij]
    congr 2 <;> simp [pairs, bitsWord]

theorem copyLead_ofWord [DecidableEq Γ] {i j : Fin k} (hij : i ≠ j) (m : ℕ) {T : Tapes k Γ}
    {pre dpre r : List Γ} (hTi : T i = .ofWord pre (bitsWord (encodeNat m) ++ r))
    (hTj : T j = .ofWord dpre []) :
    (copyLead i j).RunsWithin T (3 * (Nat.bits m).length + 1)
      (update (update T i (.ofWord (pre ++ bitsWord (encodeNat m)) r)) j
        (.ofWord (dpre ++ bitsWord (encodeNat m)) [])) := by
  have he : bitsWord (encodeNat m) = (bitsWord (pairs (Nat.bits m)) ++ [bit false] : List Γ) := by
    simp [encodeNat, pairs, bitsWord]
  have h₁ := copyLoop_ofWord hij (Nat.bits m) (T := T) (pre := pre) (dpre := dpre) (r := r)
    (by rw [hTi, he]; simp) hTj
  have h₂ := cp_ofWord (T := update (update T i (.ofWord (pre ++ bitsWord (pairs (Nat.bits m)))
      (bit false :: r))) j (.ofWord (dpre ++ bitsWord (pairs (Nat.bits m))) []))
      (pre := pre ++ bitsWord (pairs (Nat.bits m))) (rest := r)
      (dpre := dpre ++ bitsWord (pairs (Nat.bits m))) hij (bit false)
    (by simp [update_of_ne hij]) (by simp)
  refine (seq_runsWithin h₁ h₂).congr_right ?_
  simp only [update_update_update_update hij, he]
  congr 2 <;> simp

end CopyLead

/-! ## The machine -/

variable (D : Machine)

/-- The embedding of the tapes of `simTM D`. -/
def σL : Fin (D.tapes + 2) ↪ Fin (D.tapes + 4) := Fin.castLEEmb (by omega)

/-- The tape holding the leading code. -/
def iP : Fin (D.tapes + 4) := ⟨D.tapes + 2, by omega⟩
/-- The buffer tape. -/
def iB : Fin (D.tapes + 4) := ⟨D.tapes + 3, by omega⟩
/-- The marker tape. -/
def iM : Fin (D.tapes + 4) := ⟨D.tapes + 1, by omega⟩

/-- Non-blank symbols. -/
def nb (a : Fin (D.symbols + 3)) : Bool := decide (a ≠ blank)

/-- The machine keeping the leading number of the input in front of the output of `D`. -/
noncomputable def withLead : TM (D.tapes + 3 + 1) (Fin (D.symbols + 3)) :=
  copyLead 0 (iP D) ;; rewind 0 ;; rewind (iP D) ;; write (iM D) (mark D) ;;
    onTapes (σL D) (simTM D) ;; copyR 0 (iB D) (nb D) ;; erase 0 ;; copyR (iP D) 0 (nb D) ;;
    rewind (iB D) ;; copyR (iB D) 0 (nb D)

variable {D}

lemma init_tape (y : List Bool) (j : Fin (D.tapes + 1)) :
    (init D y).tape j = ((inputTapes (Γ := Fin (D.symbols + 3)) D.tapes y) j).cells := by
  funext z
  simp only [init, inputTapes]
  by_cases hj : j = 0
  · subst hj
    simp only [true_and, if_true, listCells, List.getElem?_map]
    by_cases hz : 0 ≤ z
    · rw [if_pos hz, if_pos hz]
      rcases y[z.toNat]? with _ | b
      · rfl
      · cases b <;> rfl
    · rw [if_neg hz, if_neg hz]; rfl
  · rw [if_neg (fun h => hj h.1), if_neg hj]; rfl

/-- **Specification of `simTM`.** -/
theorem simTM_runsWithin {y z : List Bool} {t : ℕ} (hD : ComputesWithin D y z t)
    {T : Machines.Tapes (D.tapes + 2) (Fin (D.symbols + 3))}
    (hT : ∀ j : Fin (D.tapes + 1), T j.castSucc = ⟨0, (init D y).tape j⟩)
    (hmk : T (mkI D) = ⟨0, markCells D⟩) :
    ∃ T', (simTM D).RunsWithin T (2 * t) T' ∧ T' 0 = Tape.ofWord [] (bitsWord z) := by
  have hR : Rel (init D y) true T :=
    ⟨fun j => hT j, hmk, fun _ => rfl, fun h => by simp [init] at h⟩
  obtain ⟨t', ht', T', hH, hT'⟩ := sim_haltsFrom t (init D y) true T rfl hR hD.1
  have hh := Main.Compose.head_natAbs_le D y 0 t
  refine ⟨T', ⟨t', by unfold runOn at hh; omega, hH⟩, ?_⟩
  have e : (runOn D y t).tape 0 = (Tape.ofWord [] (bitsWord z) : Tape (Fin (D.symbols + 3))).cells := by
    rw [hD.2, init_tape, inputTapes_zero]
  rw [hT']
  exact Tape.ext (by simp) e

section Indices

lemma iP_ne_zero : iP D ≠ 0 := by simp [iP, Fin.ext_iff]
lemma iB_ne_zero : iB D ≠ 0 := by simp [iB, Fin.ext_iff]
lemma iM_ne_zero : iM D ≠ 0 := by simp [iM, Fin.ext_iff]
lemma iP_ne_iB : iP D ≠ iB D := by simp [iP, iB, Fin.ext_iff]
lemma iP_ne_iM : iP D ≠ iM D := by simp [iP, iM, Fin.ext_iff]
lemma iB_ne_iM : iB D ≠ iM D := by simp [iB, iM, Fin.ext_iff]
lemma σL_ne_iP (i : Fin (D.tapes + 2)) : σL D i ≠ iP D := by
  simp [σL, iP, Fin.ext_iff]; omega
lemma σL_ne_iB (i : Fin (D.tapes + 2)) : σL D i ≠ iB D := by
  simp [σL, iB, Fin.ext_iff]; omega
lemma σL_zero : σL D 0 = 0 := by simp [σL]
lemma σL_mkI : σL D (mkI D) = iM D := by simp [σL, mkI, iM, Fin.ext_iff]
lemma σL_castSucc_ne_iM (j : Fin (D.tapes + 1)) : σL D j.castSucc ≠ iM D := by
  simp [σL, iM, Fin.ext_iff]; omega

end Indices

lemma nb_bitsWord (l : List Bool) : ∀ a ∈ (bitsWord l : List (Fin (D.symbols + 3))), nb D a = true :=
  fun _ ha => by simpa [nb] using bit_ne_blank_of_mem_bitsWord ha

lemma ne_blank_bitsWord (l : List Bool) : ∀ a ∈ (bitsWord l : List (Fin (D.symbols + 3))), a ≠ blank :=
  fun _ ha => bit_ne_blank_of_mem_bitsWord ha

/-- **Specification of `withLead`** on structured tapes. -/
theorem withLead_runsWithin {m : ℕ} {v z : List Bool} {t : ℕ}
    (hD : ComputesWithin D (encodeNat m ++ v) z t) :
    ∃ T', (withLead D).RunsWithin (inputTapes (D.tapes + 3) (encodeNat m ++ v))
      (2 * t + 8 * (encodeNat m).length + 8 * z.length + 10) T' ∧
      T' 0 = Tape.ofWord (bitsWord (encodeNat m ++ z)) [] := by
  set p : List (Fin (D.symbols + 3)) := bitsWord (encodeNat m) with hp
  set V : List (Fin (D.symbols + 3)) := bitsWord v with hV
  set Z : List (Fin (D.symbols + 3)) := bitsWord z with hZ
  set T0 := inputTapes (Γ := Fin (D.symbols + 3)) (D.tapes + 3) (encodeNat m ++ v) with hT0
  have hT00 : T0 0 = .ofWord [] (p ++ V) := by
    rw [hT0, inputTapes_zero]; simp [hp, hV, bitsWord]
  have hT0x : ∀ x : Fin (D.tapes + 4), x ≠ 0 → T0 x = .ofWord [] [] :=
    fun x hx => inputTapes_ne_zero _ hx
  -- 1. copy the leading code
  obtain ⟨T1, h1, f1a, f1b, f1c⟩ : ∃ T1, (copyLead 0 (iP D)).RunsWithin T0
      (3 * (Nat.bits m).length + 1) T1 ∧ T1 0 = .ofWord p V ∧ T1 (iP D) = .ofWord p [] ∧
      ∀ x, x ≠ 0 → x ≠ iP D → T1 x = T0 x :=
    ⟨_, copyLead_ofWord (iP_ne_zero (D := D)).symm m (pre := []) (dpre := []) (r := V) hT00
      (hT0x _ iP_ne_zero), by simp [update_of_ne (iP_ne_zero (D := D)).symm, hp],
      by simp [hp], fun x h0 hP => by simp [update_of_ne h0, update_of_ne hP]⟩
  -- 2. rewind tape 0
  obtain ⟨T2, h2, f2a, f2c⟩ : ∃ T2, (rewind 0).RunsWithin T1 (2 * p.length + 2) T2 ∧
      T2 0 = .ofWord [] (p ++ V) ∧ ∀ x, x ≠ 0 → T2 x = T1 x :=
    ⟨_, rewind_ofWord 0 f1a (ne_blank_bitsWord _), by simp,
      fun x h0 => by simp [update_of_ne h0]⟩
  -- 3. rewind the code tape
  obtain ⟨T3, h3, f3a, f3b, f3c⟩ : ∃ T3, (rewind (iP D)).RunsWithin T2 (2 * p.length + 2) T3 ∧
      T3 0 = .ofWord [] (p ++ V) ∧ T3 (iP D) = .ofWord [] p ∧
      ∀ x, x ≠ 0 → x ≠ iP D → T3 x = T0 x :=
    ⟨_, rewind_ofWord (iP D) (by rw [f2c _ iP_ne_zero, f1b]) (ne_blank_bitsWord _),
      by simp [update_of_ne (iP_ne_zero (D := D)).symm, f2a], by simp,
      fun x h0 hP => by simp [update_of_ne hP, f2c _ h0, f1c _ h0 hP]⟩
  -- 4. mark the origin
  obtain ⟨T4, h4, f4a, f4b, f4m, f4c⟩ : ∃ T4, (write (iM D) (mark D)).RunsWithin T3 1 T4 ∧
      T4 0 = .ofWord [] (p ++ V) ∧ T4 (iP D) = .ofWord [] p ∧ T4 (iM D) = .ofWord [] [mark D] ∧
      ∀ x, x ≠ 0 → x ≠ iP D → x ≠ iM D → T4 x = T0 x :=
    ⟨_, write_runsWithin _ _ _, by simp [update_of_ne (iM_ne_zero (D := D)).symm, f3a],
      by simp [update_of_ne (iP_ne_iM (D := D)), f3b],
      by simp [f3c _ iM_ne_zero iP_ne_iM.symm, hT0x _ iM_ne_zero, Tape.act_ofWord_stay],
      fun x h0 hP hM => by simp [update_of_ne hM, f3c _ h0 hP]⟩
  -- 5. simulate `D`
  have hsim := simTM_runsWithin hD (T := T4 ∘ σL D)
    (fun j => by
      show T4 (σL D j.castSucc) = _
      rw [init_tape]
      by_cases hj : j = 0
      · subst hj
        rw [Fin.castSucc_zero, σL_zero, f4a, inputTapes_zero]
        exact Tape.ext (by simp) (by simp [hp, hV, bitsWord])
      · have h0 : σL D j.castSucc ≠ 0 := by
          intro h; apply hj; ext; have := congrArg Fin.val h; simpa [σL] using this
        rw [f4c _ h0 (σL_ne_iP _) (σL_castSucc_ne_iM _), hT0x _ h0, inputTapes_ne_zero _ hj]
        rfl)
    (by show T4 (σL D (mkI D)) = _; rw [σL_mkI, f4m]; rfl)
  obtain ⟨T', h5', hT'0⟩ := hsim
  have h5 := onTapes_runsWithin (σL D) h5'
  obtain ⟨T5, h5, f5a, f5b, f5B⟩ : ∃ T5, (onTapes (σL D) (simTM D)).RunsWithin T4 (2 * t) T5 ∧
      T5 0 = .ofWord [] Z ∧ T5 (iP D) = .ofWord [] p ∧ T5 (iB D) = .ofWord [] [] :=
    ⟨_, h5, by rw [← σL_zero, updateTapes_apply_self, hT'0],
      by rw [updateTapes_apply_of_not_mem _ _ _ σL_ne_iP, f4b],
      by rw [updateTapes_apply_of_not_mem _ _ _ σL_ne_iB, f4c _ iB_ne_zero iP_ne_iB.symm
        iB_ne_iM, hT0x _ iB_ne_zero]⟩
  -- 6. copy the output to the buffer
  obtain ⟨T6, h6, f6a, f6b, f6B⟩ : ∃ T6, (copyR 0 (iB D) (nb D)).RunsWithin T5 (2 * Z.length) T6 ∧
      T6 0 = .ofWord Z [] ∧ T6 (iP D) = .ofWord [] p ∧ T6 (iB D) = .ofWord Z [] :=
    ⟨_, copyR_ofWord (iB_ne_zero (D := D)).symm (nb D) (pre := []) (u := Z) (rest := [])
      (by simpa using f5a) (nb_bitsWord _) (by simp [nb]) f5B,
      by simp [update_of_ne (iB_ne_zero (D := D)).symm],
      by simp [update_of_ne (iP_ne_iB (D := D)), update_of_ne (iP_ne_zero (D := D)), f5b],
      by simp⟩
  -- 7. erase tape 0
  obtain ⟨T7, h7, f7a, f7b, f7B⟩ : ∃ T7, (erase 0).RunsWithin T6 (2 * Z.length + 2) T7 ∧
      T7 0 = .ofWord [] [] ∧ T7 (iP D) = .ofWord [] p ∧ T7 (iB D) = .ofWord Z [] := by
    refine ⟨_, (erase_ofWord 0 f6a (by simpa using ne_blank_bitsWord z)).mono (by simp), by simp,
      by simp [update_of_ne (iP_ne_zero (D := D)), f6b],
      by simp [update_of_ne (iB_ne_zero (D := D)), f6B]⟩
  -- 8. write the leading code on tape 0
  obtain ⟨T8, h8, f8a, f8B⟩ : ∃ T8, (copyR (iP D) 0 (nb D)).RunsWithin T7 (2 * p.length) T8 ∧
      T8 0 = .ofWord p [] ∧ T8 (iB D) = .ofWord Z [] :=
    ⟨_, copyR_ofWord (iP_ne_zero (D := D)) (nb D) (pre := []) (u := p) (rest := [])
      (by simpa using f7b) (nb_bitsWord _) (by simp [nb]) f7a, by simp,
      by simp [update_of_ne (iB_ne_zero (D := D)), update_of_ne (iP_ne_iB (D := D)).symm, f7B]⟩
  -- 9. rewind the buffer
  obtain ⟨T9, h9, f9a, f9B⟩ : ∃ T9, (rewind (iB D)).RunsWithin T8 (2 * Z.length + 2) T9 ∧
      T9 0 = .ofWord p [] ∧ T9 (iB D) = .ofWord [] Z :=
    ⟨_, rewind_ofWord (iB D) f8B (ne_blank_bitsWord _),
      by simp [update_of_ne (iB_ne_zero (D := D)).symm, f8a], by simp⟩
  -- 10. append the output
  obtain ⟨T10, h10, f10a⟩ : ∃ T10, (copyR (iB D) 0 (nb D)).RunsWithin T9 (2 * Z.length) T10 ∧
      T10 0 = .ofWord (p ++ Z) [] :=
    ⟨_, copyR_ofWord (iB_ne_zero (D := D)) (nb D) (pre := []) (u := Z) (rest := [])
      (by simpa using f9B) (nb_bitsWord _) (by simp [nb]) f9a, by simp⟩
  have h := seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin
    (seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin h1 h2) h3) h4) h5) h6) h7)
    h8) h9) h10
  refine ⟨T10, h.mono ?_, by rw [f10a]; simp [hp, hZ, bitsWord]⟩
  have hpl : p.length = (encodeNat m).length := by simp [hp, bitsWord]
  have hZl : Z.length = z.length := by simp [hZ, bitsWord]
  have hb : 2 * (Nat.bits m).length + 1 = (encodeNat m).length := by simp [encodeNat]; omega
  omega

/-- **Keeping the leading number.** -/
theorem withLead_computesWithin {m : ℕ} {v z : List Bool} {t : ℕ}
    (hD : ComputesWithin D (encodeNat m ++ v) z t) :
    ComputesWithin (withLead D).compile (encodeNat m ++ v) (encodeNat m ++ z)
      (16 * (t + (encodeNat m ++ v).length + 1)) := by
  obtain ⟨T', h, hT'⟩ := withLead_runsWithin hD
  have hc := (withLead D).computesWithin (fun _ _ => false) h
    (y := encodeNat m ++ z) (by rw [hT']; simp [bitsWord])
  have hz := length_le_of_computesWithin hD
  refine Main.Compose.computesWithin_mono' hc ?_
  simp only [List.length_append] at hz ⊢
  omega

end Lax119563Proofs.Hardness

end Hardness_LeadMachine

/-! ### Formerly `Lax119563Proofs.Hardness.ExpMachine` -/

section Hardness_ExpMachine

/-!
# The machines of the EXPTIME reduction

* `dropTM`: a machine computing `x` from `true :: true :: x` (`drop_computesWithin`). Composed
  with a decider of a language `L`, it decides `L` on padded inputs `true :: true :: x`, which
  have length at least `2`, as the pipeline requires.
* `redTM R d`: on input `x` with `n = |x|` and `L = |bits n|`, it counts `n` in binary, writes
  `encodeNats [h, h] ++ true :: true :: x` with `h = 2^(d (L + 1)) - 1` (the code of `h` is
  `(1 1)^(d (L+1)) 0`, written with `d` passes over the counter), and runs the machine `R` on
  it (by `simTM`). So if `R` computes `z` from that word within `t` steps, `redTM R d`
  computes `z` from `x` within `2 t + 40 (d + 1) (n + 1)^2` steps (`redTM_computesWithin`).
-/

open Lax489179.TuringMachine (Machine Config Move Instruction init step run Deterministic)
open Lax119563.DeterministicTime Lax119563.BinaryEncodings

namespace Lax119563Proofs.Hardness

open Machines Machines.TM Function

/-! ## Writing runs of ones -/

section Ones

variable {Γ : Type} [TapeAlphabet Γ] [DecidableEq Γ] {k : ℕ}

/-- `n`-fold repetition of a machine. -/
def rep (M : TM k Γ) : ℕ → TM k Γ
  | 0 => nop
  | n + 1 => M ;; rep M n

/-- For each symbol of the counter tape `c`, append two ones to tape `o`. -/
def onesLoop (c o : Fin k) : TM k Γ :=
  loop (fun s => decide (s c ≠ blank))
    (act₂ c o (fun a _ => ((a, .right), (bit true, .right))) ;; writeR o (bit true))

/-- Append `2 (|u| + 1)` ones to tape `o`, where `u` is the word on the counter tape. -/
def pass (c o : Fin k) : TM k Γ :=
  writeR o (bit true) ;; writeR o (bit true) ;; onesLoop c o ;; rewind c

/-- Append the code of `2^(m (|u| + 1)) - 1`. -/
def emitOnes (c o : Fin k) (m : ℕ) : TM k Γ :=
  rep (pass c o) m ;; writeR o (bit false)

theorem onesLoop_ofWord {c o : Fin k} (hco : c ≠ o) (u : List Γ) (hu : ∀ a ∈ u, a ≠ blank) :
    ∀ (pre opre : List Γ) (T : Tapes k Γ), T c = .ofWord pre u → T o = .ofWord opre [] →
    (onesLoop c o).RunsWithin T (3 * u.length)
      (update (update T c (.ofWord (pre ++ u) [])) o
        (.ofWord (opre ++ List.replicate (2 * u.length) (bit true)) [])) := by
  induction u with
  | nil =>
    intro pre opre T hc ho
    refine ((loop_runsWithin_exit (by simp [readAll, hc])).mono (by simp)).congr_right ?_
    funext l
    by_cases hl : l = o
    · subst hl; simp [ho]
    · by_cases hl' : l = c
      · subst hl'; simp [update_of_ne hl, hc]
      · simp [update_of_ne hl, update_of_ne hl']
  | cons a u ih =>
    intro pre opre T hc ho
    have ha : a ≠ blank := hu a (by simp)
    have h₁ := act₂_runsWithin hco (fun a (_ : Γ) => ((a, Move.right), (bit true, Move.right))) T
    simp only [hc, ho, Tape.read_ofWord_cons, Tape.act_ofWord_right, List.tail_cons,
      List.tail_nil] at h₁
    have h₂ := writeR_runsWithin o (bit true)
      (update (update T c (Tape.ofWord (pre ++ [a]) u)) o (Tape.ofWord (opre ++ [bit true]) []))
    simp only [update_self, Tape.act_ofWord_right, List.tail_nil, update_idem] at h₂
    have h₃ := ih (fun b hb => hu b (by simp [hb])) (pre ++ [a]) (opre ++ [bit true] ++ [bit true])
      (update (update T c (Tape.ofWord (pre ++ [a]) u)) o
        (Tape.ofWord (opre ++ [bit true] ++ [bit true]) []))
      (by simp [update_of_ne hco]) (by simp)
    have h := loop_runsWithin_iter (c := fun s => decide (s c ≠ blank))
      (by simp [readAll, hc, ha]) (seq_runsWithin h₁ h₂) h₃
    refine (h.mono (by simp; omega)).congr_right ?_
    rw [update_update_update_update hco]
    congr 2
    · simp
    · simp only [List.append_assoc, List.length_cons]
      congr 1

theorem pass_ofWord {c o : Fin k} (hco : c ≠ o) (u : List Γ) (hu : ∀ a ∈ u, a ≠ blank)
    (opre : List Γ) (T : Tapes k Γ) (hc : T c = .ofWord [] u) (ho : T o = .ofWord opre []) :
    (pass c o).RunsWithin T (5 * u.length + 4)
      (update T o (.ofWord (opre ++ List.replicate (2 * (u.length + 1)) (bit true)) [])) := by
  have h₁ := writeR_runsWithin o (bit true) T
  rw [ho, Tape.act_ofWord_right] at h₁
  have h₂ := writeR_runsWithin o (bit true) (update T o (Tape.ofWord (opre ++ [bit true]) []))
  simp only [update_self, Tape.act_ofWord_right, List.tail_nil, update_idem] at h₂
  have h₃ := onesLoop_ofWord hco u hu [] (opre ++ [bit true] ++ [bit true])
    (update T o (Tape.ofWord (opre ++ [bit true] ++ [bit true]) []))
    (by simp [update_of_ne hco, hc]) (by simp)
  have h₄ := rewind_ofWord c (pre := u) (rest := [])
    (T := update (update (update T o (Tape.ofWord (opre ++ [bit true] ++ [bit true]) [])) c
      (Tape.ofWord ([] ++ u) [])) o
      (Tape.ofWord (opre ++ [bit true] ++ [bit true] ++ List.replicate (2 * u.length) (bit true)) []))
    (by simp [update_of_ne hco]) hu
  refine ((seq_runsWithin (seq_runsWithin (seq_runsWithin h₁ h₂) h₃) h₄).mono
    (by omega)).congr_right ?_
  funext l
  by_cases hl : l = o
  · subst hl
    simp only [update_of_ne hco.symm, update_self, List.append_assoc]
    congr 2
  · by_cases hl' : l = c
    · subst hl'; simp [update_of_ne hl, hc]
    · simp [update_of_ne hl, update_of_ne hl']

theorem rep_pass_ofWord {c o : Fin k} (hco : c ≠ o) (u : List Γ) (hu : ∀ a ∈ u, a ≠ blank) :
    ∀ (m : ℕ) (opre : List Γ) (T : Tapes k Γ), T c = .ofWord [] u → T o = .ofWord opre [] →
    (rep (pass c o) m).RunsWithin T (m * (5 * u.length + 4))
      (update T o (.ofWord (opre ++ List.replicate (2 * m * (u.length + 1)) (bit true)) [])) := by
  intro m
  induction m with
  | zero =>
    intro opre T hc ho
    refine ((nop_haltsIn T).runsWithin.mono (by simp)).congr_right ?_
    simp [← ho]
  | succ m ih =>
    intro opre T hc ho
    have h₁ := pass_ofWord hco u hu opre T hc ho
    have h₂ := ih (opre ++ List.replicate (2 * (u.length + 1)) (bit true))
      (update T o (.ofWord (opre ++ List.replicate (2 * (u.length + 1)) (bit true)) []))
      (by simp [update_of_ne hco, hc]) (by simp)
    refine ((seq_runsWithin h₁ h₂).mono (le_of_eq (by ring))).congr_right ?_
    rw [update_idem, List.append_assoc, ← List.replicate_add,
      show 2 * (u.length + 1) + 2 * m * (u.length + 1) = 2 * (m + 1) * (u.length + 1) by ring]

theorem emitOnes_ofWord {c o : Fin k} (hco : c ≠ o) (u : List Γ) (hu : ∀ a ∈ u, a ≠ blank)
    (m : ℕ) (opre : List Γ) (T : Tapes k Γ) (hc : T c = .ofWord [] u)
    (ho : T o = .ofWord opre []) :
    (emitOnes c o m).RunsWithin T (m * (5 * u.length + 4) + 1)
      (update T o (.ofWord (opre ++ (List.replicate (2 * m * (u.length + 1)) (bit true) ++
        [bit false])) [])) := by
  have h₁ := rep_pass_ofWord hco u hu m opre T hc ho
  have h₂ := writeR_runsWithin o (bit false)
    (update T o (Tape.ofWord (opre ++ List.replicate (2 * m * (u.length + 1)) (bit true)) []))
  simp only [update_self, Tape.act_ofWord_right, List.tail_nil, update_idem] at h₂
  exact (seq_runsWithin h₁ h₂).congr_right (by simp)

end Ones

/-! ## The number `h` -/

lemma bits_two_pow_sub_one (j : ℕ) : Nat.bits (2 ^ j - 1) = List.replicate j true := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : 2 ^ (j + 1) - 1 = 2 * (2 ^ j - 1) + 1 := by
      have := Nat.one_le_two_pow (n := j); rw [pow_succ]; omega
    rw [e, Nat.bit1_bits, ih, List.replicate_succ]

lemma encodeNat_two_pow_sub_one (j : ℕ) :
    encodeNat (2 ^ j - 1) = List.replicate (2 * j) true ++ [false] := by
  rw [encodeNat, bits_two_pow_sub_one]
  congr 1
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ, List.flatMap_cons, ih,
      show 2 * (j + 1) = 1 + 1 + 2 * j by ring, List.replicate_add, List.replicate_add]
    simp

/-- The horizon exponent `h = 2^(d (|bits n| + 1)) - 1`. -/
def hOf (d n : ℕ) : ℕ := 2 ^ (d * ((Nat.bits n).length + 1)) - 1

/-! ## Dropping two leading bits -/

/-- The core of the machine dropping the two leading bits. -/
def dropTM : TM 2 (Fin 3) :=
  moveR 0 ;; moveR 0 ;; copyR 0 1 (fun a => decide (a ≠ blank))

/-- The machine computing `x` from `true :: true :: x`. -/
noncomputable def dropMachine : Machine := (dropTM ;; finish 1).compile

theorem drop_computesWithin (x : List Bool) :
    ComputesWithin dropMachine (true :: true :: x) x (8 * x.length + 11) := by
  set X : List (Fin 3) := bitsWord x with hX
  set T0 := inputTapes (Γ := Fin 3) 1 (true :: true :: x) with hT0
  have h00 : T0 0 = .ofWord [] (bit true :: bit true :: X) := by
    rw [hT0, inputTapes_zero]; simp [bitsWord, hX]
  have h01 : T0 1 = .ofWord [] [] := inputTapes_ne_zero _ (by decide)
  have h₁ := moveR_runsWithin 0 T0
  rw [h00, Tape.move_ofWord_right] at h₁
  have h₂ := moveR_runsWithin 0 (update T0 0 (Tape.ofWord [bit true] (bit true :: X)))
  simp only [update_self, Tape.move_ofWord_right, update_idem, List.singleton_append] at h₂
  have h₃ := copyR_ofWord (show (0 : Fin 2) ≠ 1 by decide) (fun a => decide (a ≠ blank))
    (T := update T0 0 (Tape.ofWord [bit true, bit true] X)) (pre := [bit true, bit true])
    (u := X) (rest := []) (dpre := []) (drest := []) (by simp)
    (fun a ha => by simpa using bit_ne_blank_of_mem_bitsWord ha) (by simp)
    (by simp [h01])
  have h := seq_runsWithin (seq_runsWithin h₁ h₂) h₃
  have hc := TM.computesWithin_finish dropTM (o := 1) (by decide) (x := true :: true :: x) (y := x)
    h (pre := [bit true, bit true] ++ X) (rest := []) (opre := X) (orest := [])
    (by simp)
    (fun a ha => by
      simp only [List.append_nil, List.mem_append, List.mem_cons, List.mem_nil_iff,
        or_false] at ha
      rcases ha with (rfl | rfl) | ha
      · simp
      · simp
      · exact bit_ne_blank_of_mem_bitsWord ha)
    (by simp) (by simp [hX])
  refine Main.Compose.computesWithin_mono' hc ?_
  simp [hX, bitsWord]
  omega

/-! ## The reduction machine -/

section Red

variable (D : Machine)

/-- The reduction machine: count `n = |x|`, write `encodeNats [h, h] ++ true :: true :: x` with
`h = hOf d n`, and run `D` on it. -/
noncomputable def redTM (d : ℕ) : TM (D.tapes + 3 + 1) (Fin (D.symbols + 3)) :=
  countLen 0 (iP D) ;; emitOnes (iP D) (iB D) d ;; emitOnes (iP D) (iB D) d ;;
    writeR (iB D) (bit true) ;; writeR (iB D) (bit true) ;; rewind 0 ;; copyR 0 (iB D) (nb D) ;;
    erase 0 ;; rewind (iB D) ;; copyR (iB D) 0 (nb D) ;; rewind 0 ;;
    write (iM D) (mark D) ;; onTapes (σL D) (simTM D)

theorem redTM_deterministic (d : ℕ) : Deterministic (redTM D d).compile :=
  (redTM D d).deterministic_compile

variable {D}

/-- Tapes described by the four tapes in use (`0`, counter, output buffer, marker). -/
def St (a b c e : Machines.Tape (Fin (D.symbols + 3))) : Machines.Tapes (D.tapes + 4) (Fin (D.symbols + 3)) :=
  fun i => if i = 0 then a else if i = iP D then b else if i = iB D then c else
    if i = iM D then e else .ofWord [] []

section StLemmas

variable (a b c e a' : Machines.Tape (Fin (D.symbols + 3)))

@[simp] lemma St_zero : St a b c e 0 = a := by simp [St]
@[simp] lemma St_iP : St a b c e (iP D) = b := by simp [St, iP_ne_zero]
@[simp] lemma St_iB : St a b c e (iB D) = c := by simp [St, iB_ne_zero, iP_ne_iB.symm]
@[simp] lemma St_iM : St a b c e (iM D) = e := by
  simp [St, iM_ne_zero, iP_ne_iM.symm, iB_ne_iM.symm]

lemma St_other {i : Fin (D.tapes + 4)} (h0 : i ≠ 0) (hP : i ≠ iP D) (hB : i ≠ iB D)
    (hM : i ≠ iM D) : St a b c e i = .ofWord [] [] := by simp [St, h0, hP, hB, hM]

@[simp] lemma update_St_zero : update (St a b c e) 0 a' = St a' b c e := by
  funext i; by_cases h : i = 0
  · subst h; simp
  · simp [St, h]
@[simp] lemma update_St_iP : update (St a b c e) (iP D) a' = St a a' c e := by
  funext i; by_cases h : i = iP D
  · subst h; simp
  · simp [St, h]
@[simp] lemma update_St_iB : update (St a b c e) (iB D) a' = St a b a' e := by
  funext i; by_cases h : i = iB D
  · subst h; simp
  · simp [St, h]
@[simp] lemma update_St_iM : update (St a b c e) (iM D) a' = St a b c a' := by
  funext i; by_cases h : i = iM D
  · subst h; simp
  · simp [St, h]

end StLemmas

lemma inputTapes_eq_St (x : List Bool) :
    inputTapes (Γ := Fin (D.symbols + 3)) (D.tapes + 3) x =
      St (.ofWord [] (bitsWord x)) (.ofWord [] []) (.ofWord [] []) (.ofWord [] []) := by
  funext i
  by_cases h : i = 0
  · subst h; rw [inputTapes_zero]; simp
  · rw [inputTapes_ne_zero _ h]
    simp [St, h]

lemma length_natWord (n : ℕ) : (natWord n : List (Fin (D.symbols + 3))).length =
    (Nat.bits n).length := by simp [natWord]

/-- The word written by `redTM`. -/
def redInput (d : ℕ) (x : List Bool) : List Bool :=
  encodeNats [hOf d x.length, hOf d x.length] ++ true :: true :: x

lemma bitsWord_encodeNat_hOf {Γ : Type} [TapeAlphabet Γ] (d n : ℕ) :
    (bitsWord (encodeNat (hOf d n)) : List Γ) =
      List.replicate (2 * d * ((Nat.bits n).length + 1)) (bit true) ++ [bit false] := by
  rw [hOf, encodeNat_two_pow_sub_one]
  simp [bitsWord, List.map_replicate, Nat.mul_assoc]

lemma length_redInput (d : ℕ) (x : List Bool) :
    (redInput d x).length = 2 * (2 * d * ((Nat.bits x.length).length + 1) + 1) + x.length + 2 := by
  have e := congrArg List.length (bitsWord_encodeNat_hOf (Γ := Fin 3) d x.length)
  simp only [bitsWord, List.length_map, List.length_append, List.length_replicate,
    List.length_singleton] at e
  simp [redInput, encodeNats, e]
  ring

/-- **Specification of `redTM`.** -/
theorem redTM_runsWithin (d : ℕ) {x z : List Bool} {t : ℕ}
    (hD : ComputesWithin D (redInput d x) z t) :
    ∃ T', (redTM D d).RunsWithin (inputTapes (D.tapes + 3) x)
      (x.length * (4 * Nat.size x.length + 7) + 2 * (d * (5 * (Nat.bits x.length).length + 4) + 1)
        + 2 + (2 * x.length + 2) + 2 * x.length + (2 * x.length + 2)
        + 3 * (2 * (redInput d x).length + 2) + 1 + 2 * t) T' ∧
      T' 0 = Tape.ofWord [] (bitsWord z) := by
  set X : List (Fin (D.symbols + 3)) := bitsWord x with hX
  set U : List (Fin (D.symbols + 3)) := natWord x.length with hU
  set E : List (Fin (D.symbols + 3)) := bitsWord (encodeNat (hOf d x.length)) with hE
  set Y : List (Fin (D.symbols + 3)) := bitsWord (redInput d x) with hY
  set e₀ : Machines.Tape (Fin (D.symbols + 3)) := .ofWord [] [] with he₀
  have hXb : ∀ a ∈ X, a ≠ blank := fun a ha => bit_ne_blank_of_mem_bitsWord ha
  have hUb : ∀ a ∈ U, a ≠ blank := fun a ha => mem_natWord_ne_blank ha
  have hYb : ∀ a ∈ Y, a ≠ blank := fun a ha => bit_ne_blank_of_mem_bitsWord ha
  have hEeq : E = List.replicate (2 * d * (U.length + 1)) (bit true) ++ [bit false] := by
    rw [hE, bitsWord_encodeNat_hOf, hU, length_natWord]
  have hYeq : Y = E ++ E ++ [bit true, bit true] ++ X := by
    simp [hY, hE, hX, redInput, encodeNats, bitsWord]
  have hXl : X.length = x.length := by simp [hX, bitsWord]
  have hUl : U.length = (Nat.bits x.length).length := by rw [hU, length_natWord]
  -- 1. count
  have h1 := countLen_ofWord (iP_ne_zero (D := D)).symm X hXb [] 0 (St (.ofWord [] X) e₀ e₀ e₀)
    (by simp) (by simp [he₀, natWord])
  simp only [update_St_zero, update_St_iP, List.nil_append, zero_add] at h1
  rw [hXl] at h1
  -- 2., 3. the two codes of `h`
  have h2 := emitOnes_ofWord (iP_ne_iB (D := D)) U hUb d [] (St (.ofWord X []) (.ofWord [] U) e₀ e₀)
    (by simp [hU]) (by simp [he₀])
  rw [update_St_iB, List.nil_append, ← hEeq] at h2
  have h3 := emitOnes_ofWord (iP_ne_iB (D := D)) U hUb d E (St (.ofWord X []) (.ofWord [] U)
    (.ofWord E []) e₀) (by simp) (by simp)
  rw [update_St_iB, ← hEeq] at h3
  -- 4., 5. the padding
  have h4 := writeR_runsWithin (iB D) (bit true) (St (.ofWord X []) (.ofWord [] U)
    (.ofWord (E ++ E) []) e₀)
  simp only [St_iB, Tape.act_ofWord_right, List.tail_nil, update_St_iB] at h4
  have h5 := writeR_runsWithin (iB D) (bit true) (St (.ofWord X []) (.ofWord [] U)
    (.ofWord (E ++ E ++ [bit true]) []) e₀)
  simp only [St_iB, Tape.act_ofWord_right, List.tail_nil, update_St_iB] at h5
  -- 6. rewind the input
  have h6 := rewind_ofWord 0 (T := St (.ofWord X []) (.ofWord [] U)
    (.ofWord (E ++ E ++ [bit true] ++ [bit true]) []) e₀) (pre := X) (rest := []) (by simp) hXb
  simp only [update_St_zero, List.append_nil] at h6
  -- 7. copy the input
  have h7 := copyR_ofWord (iB_ne_zero (D := D)).symm (nb D) (pre := []) (u := X) (rest := [])
    (T := St (.ofWord [] X) (.ofWord [] U) (.ofWord (E ++ E ++ [bit true] ++ [bit true]) []) e₀)
    (dpre := E ++ E ++ [bit true] ++ [bit true]) (drest := []) (by simp)
    (fun a ha => by simpa [nb] using hXb a ha) (by simp [nb]) (by simp)
  simp only [update_St_zero, update_St_iB, List.nil_append, List.drop_nil] at h7
  rw [show E ++ E ++ [bit true] ++ [bit true] ++ X = Y by rw [hYeq]; simp] at h7
  -- 8. erase tape 0
  have h8 := erase_ofWord 0 (T := St (.ofWord X []) (.ofWord [] U) (.ofWord Y []) e₀)
    (pre := X) (rest := []) (by simp) (by simpa using hXb)
  simp only [update_St_zero] at h8
  -- 9. rewind the buffer
  have h9 := rewind_ofWord (iB D) (T := St (.ofWord [] []) (.ofWord [] U) (.ofWord Y []) e₀)
    (pre := Y) (rest := []) (by simp) hYb
  simp only [update_St_iB, List.append_nil] at h9
  -- 10. copy back
  have h10 := copyR_ofWord (iB_ne_zero (D := D)) (nb D) (pre := []) (u := Y) (rest := [])
    (T := St (.ofWord [] []) (.ofWord [] U) (.ofWord [] Y) e₀)
    (dpre := []) (drest := []) (by simp)
    (fun a ha => by simpa [nb] using hYb a ha) (by simp [nb]) (by simp)
  simp only [update_St_zero, update_St_iB, List.nil_append, List.drop_nil] at h10
  -- 11. rewind tape 0
  have h11 := rewind_ofWord 0 (T := St (.ofWord Y []) (.ofWord [] U) (.ofWord Y []) e₀)
    (pre := Y) (rest := []) (by simp) hYb
  simp only [update_St_zero, List.append_nil] at h11
  -- 12. the mark
  have h12 := write_runsWithin (iM D) (mark D) (St (.ofWord [] Y) (.ofWord [] U) (.ofWord Y []) e₀)
  simp only [St_iM, he₀, Tape.act_ofWord_stay, List.tail_nil, update_St_iM] at h12
  -- 13. simulate `D`
  set T12 := St (.ofWord [] Y) (.ofWord [] U) (.ofWord Y []) (.ofWord [] [mark D]) with hT12
  have hsim := simTM_runsWithin hD (T := T12 ∘ σL D)
    (fun j => by
      show T12 (σL D j.castSucc) = _
      rw [init_tape]
      by_cases hj : j = 0
      · subst hj
        rw [Fin.castSucc_zero, σL_zero, hT12, St_zero, inputTapes_zero]
        exact Tape.ext (by simp) (by simp [hY, bitsWord])
      · have h0 : σL D j.castSucc ≠ 0 := by
          intro h; apply hj; ext; have := congrArg Fin.val h; simpa [σL] using this
        rw [hT12, St_other _ _ _ _ h0 (σL_ne_iP _) (σL_ne_iB _) (σL_castSucc_ne_iM _),
          inputTapes_ne_zero _ hj]
        rfl)
    (by show T12 (σL D (mkI D)) = _; rw [σL_mkI, hT12, St_iM]; rfl)
  obtain ⟨T', h13', hT'0⟩ := hsim
  have h13 := onTapes_runsWithin (σL D) h13'
  have h := seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin
    (seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin
    (seq_runsWithin (seq_runsWithin h1 h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13
  rw [inputTapes_eq_St]
  refine ⟨_, h.mono ?_, by rw [← σL_zero, updateTapes_apply_self, hT'0]⟩
  have hYl : Y.length = (redInput d x).length := by simp [hY, bitsWord]
  rw [hUl] at *
  simp only [List.length_nil, List.append_nil, hYl, hXl]
  omega

end Red

end Lax119563Proofs.Hardness

end Hardness_ExpMachine

/-! ### Formerly `Lax119563Proofs.Hardness.SizeBound` -/

section Hardness_SizeBound

/-!
# The size parameter of an implicit parity system

Every coordinate domain has at most `k 2^ℓ` coordinates, and `nnz(B_e) ≤ (2 + ℓ) k 2^ℓ`: the
`k - 1` block-parity rows have at most `|𝔠_e| + 2^ℓ (k - 1) ≤ 2 k 2^ℓ` nonzero entries on
`𝔠_e` (a coordinate of block `i < k - 1` meets only row `i`, those of the last block meet all
of them), and the `ℓ` checksum rows at most `ℓ k 2^ℓ`. Hence
`S ≤ |W| k 2^ℓ + (k + 1) |𝓔| (2 + ℓ) k 2^ℓ` (`sizeParameter_le`).
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler

namespace Lax119563Proofs.Hardness

variable {k ℓ w : ℕ}

lemma card_coord : Fintype.card (Coord k ℓ) = k * 2 ^ ℓ := by
  simp [Coord, BlockCoord, Fintype.card_prod, ZMod.card]

lemma card_domain_le (D : Finset (Coord k ℓ)) : D.card ≤ k * 2 ^ ℓ :=
  card_coord (k := k) (ℓ := ℓ) ▸ D.card_le_univ

/-- The injection used to count the nonzero entries of `B_e`. -/
def nnzMap (k ℓ : ℕ) : (Fin (k - 1) ⊕ Fin ℓ) × Coord k ℓ → (Fin 2 ⊕ Fin ℓ) × Coord k ℓ
  | (.inl i, c) => if (c.1 : ℕ) = i then (.inl 0, c) else (.inl 1, (⟨i, by omega⟩, c.2))
  | (.inr t, c) => (.inr t, c)

open Classical in
lemma nnz_le (e : Schema k ℓ w) : nnz e ≤ (2 + ℓ) * (k * 2 ^ ℓ) := by
  unfold nnz
  have hcard : Fintype.card ((Fin 2 ⊕ Fin ℓ) × Coord k ℓ) = (2 + ℓ) * (k * 2 ^ ℓ) := by
    rw [Fintype.card_prod, Fintype.card_sum, card_coord]; simp
  rw [← hcard, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (nnzMap k ℓ) (fun _ _ => Finset.mem_coe.mpr
    (Finset.mem_univ _)) ?_
  rintro ⟨r, c⟩ hx ⟨r', c'⟩ hx' heq
  simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_univ, true_and,
    Set.mem_ofPred_eq] at hx hx'
  rcases r with i | t <;> rcases r' with i' | t'
  · simp only [checkMatrix, Matrix.of_apply, ne_eq, ite_eq_right_iff, one_ne_zero,
      imp_false, not_not] at hx hx'
    simp only [nnzMap] at heq
    split_ifs at heq with h1 h2 h2
    · simp only [Prod.mk.injEq, true_and] at heq
      subst heq
      have : i = i' := Fin.ext (by omega)
      subst this; rfl
    · simp at heq
    · simp at heq
    · simp only [Prod.mk.injEq, Fin.mk.injEq, true_and] at heq
      obtain ⟨hii, hc2⟩ := heq
      have hi : i = i' := Fin.ext hii
      subst hi
      have hc1 : c.1 = c'.1 := Fin.ext (by omega)
      have : c = c' := Prod.ext hc1 hc2
      subst this; rfl
  · simp only [nnzMap] at heq; split_ifs at heq <;> simp at heq
  · simp only [nnzMap] at heq; split_ifs at heq <;> simp at heq
  · simp only [nnzMap, Prod.mk.injEq, Sum.inr.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq; rfl

/-- **The size parameter.** -/
theorem sizeParameter_le (I : ImplicitParitySystem k ℓ) :
    matrixSize I ≤ I.numLocations * (k * 2 ^ ℓ) +
      (k + 1) * (I.schemas.length * ((2 + ℓ) * (k * 2 ^ ℓ))) := by
  unfold matrixSize
  have h1 : ∑ v, (I.domain v).card ≤ I.numLocations * (k * 2 ^ ℓ) := by
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin I.numLocations))
      (fun v => (I.domain v).card) (k * 2 ^ ℓ) (fun v _ => card_domain_le _)
    simpa using this
  have h2 : (I.schemas.map nnz).sum ≤ I.schemas.length * ((2 + ℓ) * (k * 2 ^ ℓ)) := by
    have := List.sum_le_card_nsmul (I.schemas.map nnz) ((2 + ℓ) * (k * 2 ^ ℓ))
      (fun x hx => by
        obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
        exact nnz_le e)
    simpa using this
  have := Nat.mul_le_mul_left (k + 1) h2
  omega

end Lax119563Proofs.Hardness

end Hardness_SizeBound

/-! ### Formerly `Lax119563Proofs.Hardness.Pipeline` -/

section Hardness_Pipeline

/-!
# From deterministic machine runs to WL instances

The common pipeline of the hardness results (EXPTIME-hardness, XP-hardness, and the
exponential lower bound): for a deterministic machine `M`, an input `x`, a horizon `2^h` and
a number `s` of data blocks, the packed implicit parity system of
`Lax119563.PackedRepresentation.packed_representation` is compiled by
`Lax119563.MatrixCompiler.matrix_compiler` into a pair of colored graphs, and the dimension
`s + 1` is put in front of their encoding.

**`pipeline`**: there are an absolute exponent `c` and, for every deterministic `M`, a
deterministic machine `R` and a constant `C` such that for `2 ≤ |x|`, `2 ≤ h`, `|x| ≤ 2^h`,
`2 ≤ s ≤ h + 2`, with `ℓ = packedWidth |x| h s`, there are graphs `G₀, G₁` with
* if `M` halts on `x` within `2^h` steps, then `M` accepts `x` iff `(s+1)`-WL distinguishes
  `G₀` and `G₁`;
* `|V(G₀)| + |V(G₁)| ≤ C (s+1)^2 2^ℓ (ℓ+1) (h+1)^2`;
* `R` computes `encodeWLInstance (s+1) G₀ G₁` from `encodeNats [h, s] ++ x` within
  `C (s 2^ℓ (h+1))^c` steps.

The machine `R` composes (`Main.Compose.compose_computesWithin`) the generator of the packed
system with `withLead` of the machine of the matrix compiler, which keeps the leading number
`k = s + 1` of the encoding of the system in front of the encoding of the graph pair.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.BinaryEncodings
  Lax119563.DeterministicTime Lax119563.PebbleGame Lax119563.ImplicitSystemEncodings
  Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.PackedRepresentation
  Lax119563.WLProblems
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Hardness

/-- The game clauses of the matrix compiler give the WL characterization. -/
lemma distinguishes_iff_conflict {k ℓ : ℕ} (hk : 2 ≤ k) (I : ImplicitParitySystem k ℓ)
    {G₀ G₁ : ColoredGraph} {Ck Λ' : ℕ}
    (hsp : ∀ τ : ℕ, I.conflictRound = τ → SpoilerWinsWithin (k + 1) (Ck * Λ' * (τ + 1)) G₀ G₁)
    (hdu : ∀ r : ℕ, (r : ℕ∞) + 1 ≤ I.conflictRound → DuplicatorSurvives (k + 1) r G₀ G₁) :
    Distinguishes k G₀ G₁ ↔ I.conflictRound < ⊤ := by
  constructor
  · intro hd
    by_contra hlt
    have htop : I.conflictRound = ⊤ := not_lt_top_iff.mp hlt
    have hw : DuplicatorWins (k + 1) G₀ G₁ := fun r => hdu r (by rw [htop]; exact le_top)
    exact (Lax119563.GameCharacterization.duplicatorWins_iff hk _ _).mp hw hd
  · intro hlt
    obtain ⟨τ, hτ⟩ := ENat.ne_top_iff_exists.mp hlt.ne
    obtain ⟨r, -, hr⟩ := Lax119563.GameCharacterization.distinguishesAfter_of_spoilerWinsWithin hk (hsp τ hτ.symm)
    exact ⟨r, hr⟩

/-! ## Encodings -/

lemma encodeNats_cons (a : ℕ) (l : List ℕ) : encodeNats (a :: l) = encodeNat a ++ encodeNats l := by
  simp [encodeNats]

lemma encodeSystem_eq {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ) :
    encodeSystem I = encodeNat k ++ encodeNats ((systemDescription I).tail) := by
  rw [encodeSystem, ← encodeNats_cons]
  congr 1

lemma encodeWLInstance_eq (k : ℕ) (G H : ColoredGraph) :
    encodeWLInstance k G H = encodeNat k ++ encodeGraphPair G H := by
  rw [encodeWLInstance, wlWord, encodeNats_cons, encodeGraphPair]

lemma length_encodeNat_le (m : ℕ) : (encodeNat m).length ≤ 2 * m + 1 := by
  have h1 : (Nat.bits m).length ≤ m := by
    rw [Nat.size_eq_bits_len, Nat.size_le]; exact Nat.lt_two_pow_self
  simp [encodeNat]; omega

/-! ## Arithmetic -/

/-- The size bound. -/
lemma size_arith {L E s Q ℓ A : ℕ} (hL : L ≤ A) (hE : E ≤ A) :
    L * ((s + 1) * Q) + (s + 1 + 1) * (E * ((2 + ℓ) * ((s + 1) * Q))) ≤
      5 * A * (s + 1) ^ 2 * Q * (ℓ + 1) := by
  have e1 : L * ((s + 1) * Q) ≤ A * ((s + 1) * Q) := Nat.mul_le_mul_right _ hL
  have e2 : (s + 1 + 1) * (E * ((2 + ℓ) * ((s + 1) * Q))) ≤
      (2 * (s + 1)) * (A * ((2 * (ℓ + 1)) * ((s + 1) * Q))) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul hE (Nat.mul_le_mul_right _ (by omega)))
  have e3 : A * ((s + 1) * Q) ≤ A * (s + 1) ^ 2 * Q * (ℓ + 1) := by
    have : (s + 1) * 1 ≤ (s + 1) * (s + 1) := Nat.mul_le_mul_left _ (by omega)
    calc A * ((s + 1) * Q) = A * ((s + 1) * 1) * Q * 1 := by ring
      _ ≤ A * ((s + 1) * (s + 1)) * Q * (ℓ + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)) (by omega)
      _ = _ := by ring
  have e4 : (2 * (s + 1)) * (A * ((2 * (ℓ + 1)) * ((s + 1) * Q))) =
      4 * (A * (s + 1) ^ 2 * Q * (ℓ + 1)) := by ring
  have e5 : 5 * A * (s + 1) ^ 2 * Q * (ℓ + 1) = 5 * (A * (s + 1) ^ 2 * Q * (ℓ + 1)) := by ring
  omega

/-- The time bound. -/
lemma time_arith {X xin T1 H S T2 Cs Cc cp cc : ℕ} (hX : 1 ≤ X) (hxin : xin ≤ 5 * X)
    (hT1 : T1 ≤ Cs * X ^ (cp + 1)) (hH : H ≤ xin + T1) (hS : S ≤ 20 * Cs * X ^ 2)
    (hT2 : T2 ≤ Cc * (H + S + 2) ^ (cc + 1)) :
    2 * T1 + 16 * (T2 + H + 1) + 3 ≤
      (2 * Cs + 16 * Cc * (21 * Cs + 7) ^ (cc + 1) + 16 * (5 + Cs) + 19) *
        X ^ ((cp + 2) * (cc + 1)) := by
  obtain ⟨P, hP⟩ : ∃ P, P = X ^ (cp + 2) := ⟨_, rfl⟩
  have hP1 : 1 ≤ P := hP ▸ Nat.one_le_pow _ _ hX
  have hXP : X ≤ P := hP ▸ (by simpa using Nat.pow_le_pow_right hX (show 1 ≤ cp + 2 by omega))
  have hX1P : X ^ (cp + 1) ≤ P := hP ▸ Nat.pow_le_pow_right hX (by omega)
  have hX2P : X ^ 2 ≤ P := hP ▸ Nat.pow_le_pow_right hX (by omega)
  have hPe : X ^ ((cp + 2) * (cc + 1)) = P ^ (cc + 1) := by rw [hP, pow_mul]
  have hPP : P ≤ P ^ (cc + 1) := by simpa using Nat.pow_le_pow_right hP1 (show 1 ≤ cc + 1 by omega)
  have hT1' : T1 ≤ Cs * P := hT1.trans (Nat.mul_le_mul_left _ hX1P)
  have hH' : H ≤ (5 + Cs) * P := by
    have : 5 * X ≤ 5 * P := Nat.mul_le_mul_left _ hXP
    have : (5 + Cs) * P = 5 * P + Cs * P := by ring
    omega
  have hS' : S ≤ 20 * Cs * P := hS.trans (Nat.mul_le_mul_left _ hX2P)
  have hHS : H + S + 2 ≤ (21 * Cs + 7) * P := by
    have : (21 * Cs + 7) * P = (5 + Cs) * P + 20 * Cs * P + 2 * P := by ring
    omega
  have hT2' : T2 ≤ Cc * (21 * Cs + 7) ^ (cc + 1) * P ^ (cc + 1) := by
    calc T2 ≤ Cc * (H + S + 2) ^ (cc + 1) := hT2
      _ ≤ Cc * ((21 * Cs + 7) * P) ^ (cc + 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hHS _)
      _ = _ := by rw [mul_pow, mul_assoc]
  rw [hPe]
  generalize P ^ (cc + 1) = Pe at hPP hT2' ⊢
  generalize (21 * Cs + 7) ^ (cc + 1) = B at hT2' ⊢
  have a1 : Cs * P ≤ Cs * Pe := Nat.mul_le_mul_left _ hPP
  have a2 : (5 + Cs) * P ≤ (5 + Cs) * Pe := Nat.mul_le_mul_left _ hPP
  have key : (2 * Cs + 16 * Cc * B + 16 * (5 + Cs) + 19) * Pe =
      2 * (Cs * Pe) + 16 * (Cc * B * Pe) + 16 * ((5 + Cs) * Pe) + 19 * Pe := by ring
  rw [key]
  omega

lemma X_facts {s Q h : ℕ} (hs : 1 ≤ s) (hQ : 1 ≤ Q) :
    h + 1 ≤ s * Q * (h + 1) ∧ s ≤ s * Q * (h + 1) ∧ Q ≤ s * Q * (h + 1) ∧
      s * Q ≤ s * Q * (h + 1) := by
  have hsQ : 1 ≤ s * Q := Nat.one_le_iff_ne_zero.mpr (by positivity)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using Nat.mul_le_mul_right (h + 1) hsQ
  · calc s = s * 1 * 1 := by ring
      _ ≤ s * Q * (h + 1) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hQ) (by omega)
  · calc Q = 1 * Q * 1 := by ring
      _ ≤ s * Q * (h + 1) := Nat.mul_le_mul (Nat.mul_le_mul_right _ hs) (by omega)
  · simpa using Nat.mul_le_mul_left (s * Q) (show 1 ≤ h + 1 by omega)

lemma T1_le {Cs s Q h cp : ℕ} (hs : 1 ≤ s) (hQ : 1 ≤ Q) :
    Cs * s * Q * (h + 1) ^ cp ≤ Cs * (s * Q * (h + 1)) ^ (cp + 1) := by
  obtain ⟨h1, -, -, h4⟩ := X_facts (h := h) hs hQ
  calc Cs * s * Q * (h + 1) ^ cp = Cs * (s * Q) * (h + 1) ^ cp := by ring
    _ ≤ Cs * (s * Q * (h + 1)) * (s * Q * (h + 1)) ^ cp :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ h4) (Nat.pow_le_pow_left h1 _)
    _ = _ := by ring

lemma S_le {S Cs s Q h ℓ : ℕ} (hS : S ≤ 5 * (Cs * (h + 1) ^ 2) * (s + 1) ^ 2 * Q * (ℓ + 1))
    (hℓ : ℓ + 1 ≤ Q) (hs : 1 ≤ s) : S ≤ 20 * Cs * (s * Q * (h + 1)) ^ 2 := by
  refine hS.trans ?_
  have h2 : (s + 1) ^ 2 ≤ 4 * s ^ 2 := by
    have : s + 1 ≤ 2 * s := by omega
    calc (s + 1) ^ 2 ≤ (2 * s) ^ 2 := Nat.pow_le_pow_left this 2
      _ = 4 * s ^ 2 := by ring
  calc 5 * (Cs * (h + 1) ^ 2) * (s + 1) ^ 2 * Q * (ℓ + 1)
      ≤ 5 * (Cs * (h + 1) ^ 2) * (4 * s ^ 2) * Q * Q :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)) hℓ
    _ = _ := by ring

lemma T2_le {Cc HS cc : ℕ} :
    Cc * HS * Nat.log 2 (HS + 2) ^ cc ≤ Cc * (HS + 2) ^ (cc + 1) := by
  calc Cc * HS * Nat.log 2 (HS + 2) ^ cc ≤ Cc * (HS + 2) * (HS + 2) ^ cc :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
          (Nat.pow_le_pow_left (Nat.log_le_self 2 _) _)
    _ = _ := by ring

lemma one_le_packedWidth (n h s : ℕ) : 1 ≤ packedWidth n h s :=
  le_trans (Nat.clog_pos (by norm_num) (by omega)) (le_max_left _ _)

lemma length_add_two_le (n h s : ℕ) : n + 2 ≤ 2 ^ packedWidth n h s :=
  (Nat.le_pow_clog (by norm_num) _).trans
    (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))

/-- **The pipeline from deterministic machine runs to WL instances.** -/
theorem pipeline : ∃ c : ℕ, ∀ M : Machine, Deterministic M →
    ∃ R : Machine, Deterministic R ∧ ∃ C : ℕ,
      ∀ (x : List Bool) (h s : ℕ), 2 ≤ x.length → 2 ≤ h → x.length ≤ 2 ^ h → 2 ≤ s →
        s ≤ h + 2 →
        ∃ G₀ G₁ : ColoredGraph,
          ((runOn M x (2 ^ h)).answer.isSome → (Accepts M x ↔ Distinguishes (s + 1) G₀ G₁)) ∧
          G₀.n + G₁.n ≤ C * (s + 1) ^ 2 * 2 ^ packedWidth x.length h s *
            (packedWidth x.length h s + 1) * (h + 1) ^ 2 ∧
          ComputesWithin R (encodeNats [h, s] ++ x) (encodeWLInstance (s + 1) G₀ G₁)
            (C * (s * 2 ^ packedWidth x.length h s * (h + 1)) ^ c) := by
  obtain ⟨cp, hpack⟩ := packed_representation
  obtain ⟨compile, ⟨Cn, hgame⟩, ⟨Mc, -, Cc, cc, hMc⟩⟩ := matrix_compiler
  refine ⟨(cp + 2) * (cc + 1), fun M hM => ?_⟩
  obtain ⟨sys, Cs, hsys, Rp, -, hRp⟩ := hpack M hM
  obtain ⟨Kt, hKt⟩ : ∃ K, K = 2 * Cs + 16 * Cc * (21 * Cs + 7) ^ (cc + 1) + 16 * (5 + Cs) + 19 :=
    ⟨_, rfl⟩
  refine ⟨(Main.Compose.comp Rp (withLead Mc).compile false fun _ => false).toMachine,
    Main.AMachine.toMachine_deterministic _, 5 * Cn * Cs + Kt,
    fun x h s hx hh hxh hs hsh => ?_⟩
  have hℓ1 := one_le_packedWidth x.length h s
  have hQ := length_add_two_le x.length h s
  obtain ⟨hcorr, hloc, hsch⟩ := hsys x h s hx hh hxh hs hsh
  obtain ⟨Ck, hCk⟩ := hgame (s + 1) (by omega)
  obtain ⟨hsp, hdu, hsize, -⟩ := hCk _ hℓ1 (sys x h s)
  have hSz : matrixSize (sys x h s) ≤ 5 * (Cs * (h + 1) ^ 2) * (s + 1) ^ 2 *
      2 ^ packedWidth x.length h s * (packedWidth x.length h s + 1) :=
    (sizeParameter_le _).trans (size_arith hloc hsch)
  refine ⟨(compile (sys x h s)).1, (compile (sys x h s)).2, fun hhalt => ?_, ?_, ?_⟩
  · exact (hcorr hhalt).symm.trans (distinguishes_iff_conflict (by omega) _ hsp hdu).symm
  · calc _ ≤ Cn * matrixSize (sys x h s) := hsize
      _ ≤ Cn * (5 * (Cs * (h + 1) ^ 2) * (s + 1) ^ 2 * 2 ^ packedWidth x.length h s *
            (packedWidth x.length h s + 1)) := Nat.mul_le_mul_left _ hSz
      _ = 5 * Cn * Cs * (s + 1) ^ 2 * 2 ^ packedWidth x.length h s *
            (packedWidth x.length h s + 1) * (h + 1) ^ 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
            (Nat.mul_le_mul_right _ (by omega))))
  · have h1 := hRp x h s hx hh hxh hs hsh
    have h2 := hMc (s + 1) (by omega) _ hℓ1 (sys x h s)
    rw [encodeSystem_eq] at h2
    have h3 := withLead_computesWithin h2
    rw [← encodeSystem_eq, ← encodeWLInstance_eq] at h3
    have hxin2 : 2 ≤ (encodeNats [h, s] ++ x).length := by simp; omega
    have hc := Main.Compose.compose_computesWithin Rp (withLead Mc).compile false
      (fun _ => false) hxin2 h1 h3
    refine Main.Compose.computesWithin_mono' hc ?_
    obtain ⟨hX1, hX2, hX3, -⟩ := X_facts (h := h) (show 1 ≤ s by omega)
      (show 1 ≤ 2 ^ packedWidth x.length h s by omega)
    have hxin : (encodeNats [h, s] ++ x).length ≤
        5 * (s * 2 ^ packedWidth x.length h s * (h + 1)) := by
      have e1 := length_encodeNat_le h
      have e2 := length_encodeNat_le s
      simp only [encodeNats, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.length_append]
      omega
    have hH := length_le_of_computesWithin h1
    have hl : packedWidth x.length h s + 1 ≤ 2 ^ packedWidth x.length h s :=
      Nat.lt_two_pow_self
    have ht := time_arith (Cs := Cs) (Cc := Cc) (cp := cp) (cc := cc)
      (X := s * 2 ^ packedWidth x.length h s * (h + 1)) (by omega) hxin
      (T1_le (show 1 ≤ s by omega) (by omega)) hH (S_le hSz hl (by omega)) T2_le
    rw [← hKt] at ht
    refine le_trans ?_ (ht.trans (Nat.mul_le_mul_right _ (by omega)))
    exact le_rfl

/-- **The pipeline, stated with the language `WLDistinguishing`.** The produced instance has
dimension `s + 1` as its leading number. -/
theorem pipeline_language : ∃ c : ℕ, ∀ M : Machine, Deterministic M →
    ∃ R : Machine, Deterministic R ∧ ∃ C : ℕ,
      ∀ (x : List Bool) (h s : ℕ), 2 ≤ x.length → 2 ≤ h → x.length ≤ 2 ^ h → 2 ≤ s →
        s ≤ h + 2 →
        ∃ G₀ G₁ : ColoredGraph,
          ((runOn M x (2 ^ h)).answer.isSome →
            (Accepts M x ↔ encodeWLInstance (s + 1) G₀ G₁ ∈ WLDistinguishing)) ∧
          leadingNat (encodeWLInstance (s + 1) G₀ G₁) = s + 1 ∧
          G₀.n + G₁.n ≤ C * (s + 1) ^ 2 * 2 ^ packedWidth x.length h s *
            (packedWidth x.length h s + 1) * (h + 1) ^ 2 ∧
          ComputesWithin R (encodeNats [h, s] ++ x) (encodeWLInstance (s + 1) G₀ G₁)
            (C * (s * 2 ^ packedWidth x.length h s * (h + 1)) ^ c) := by
  obtain ⟨c, hc⟩ := pipeline
  refine ⟨c, fun M hM => ?_⟩
  obtain ⟨R, hR, C, hC⟩ := hc M hM
  refine ⟨R, hR, C, fun x h s hx hh hxh hs hsh => ?_⟩
  obtain ⟨G₀, G₁, h1, h2, h3⟩ := hC x h s hx hh hxh hs hsh
  exact ⟨G₀, G₁, fun hh => (h1 hh).trans (encodeWLInstance_mem_iff _ _ _).symm,
    leadingNat_encodeWLInstance _ _ _, h2, h3⟩

end Lax119563Proofs.Hardness

end Hardness_Pipeline

/-! ### Formerly `Lax119563Proofs.Hardness.PipelineLen` -/

section Hardness_PipelineLen

/-!
# The pipeline with a bound on the length of the produced instance

`pipeline_len` is `pipeline` with a bound on the length of the produced WL instance instead of
the vertex bound: by `Lax119563.MatrixCompiler.matrix_compiler` the encoding of the compiled
graph pair has length `O((S + 1) log (S + 2))`. This is used for the exponential lower bound,
which measures time in the length of the instance.
-/

open Lax119563.ColoredGraphs Lax119563.WeisfeilerLeman Lax119563.BinaryEncodings
  Lax119563.DeterministicTime Lax119563.PebbleGame Lax119563.ImplicitSystemEncodings
  Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.PackedRepresentation
  Lax119563.WLProblems
open Lax489179.TuringMachine (Machine Deterministic)

namespace Lax119563Proofs.Hardness

/-- **The pipeline, with the length of the produced instance.** -/
theorem pipeline_len : ∃ c Cl : ℕ, ∀ M : Machine, Deterministic M →
    ∃ R : Machine, Deterministic R ∧ ∃ C Cs : ℕ,
      ∀ (x : List Bool) (h s : ℕ), 2 ≤ x.length → 2 ≤ h → x.length ≤ 2 ^ h → 2 ≤ s →
        s ≤ h + 2 →
        ∃ G₀ G₁ : ColoredGraph,
          (HaltsWithin M x (2 ^ h) → (Accepts M x ↔ Distinguishes (s + 1) G₀ G₁)) ∧
          (encodeWLInstance (s + 1) G₀ G₁).length ≤ 2 * (s + 1) + 1 +
            Cl * (Cs * (h + 1) ^ 2 * (s + 1) ^ 2 * 2 ^ packedWidth x.length h s *
              (packedWidth x.length h s + 1) + 1) *
            (Nat.log 2 (Cs * (h + 1) ^ 2 * (s + 1) ^ 2 * 2 ^ packedWidth x.length h s *
              (packedWidth x.length h s + 1) + 2) + 1) ∧
          ComputesWithin R (encodeNats [h, s] ++ x) (encodeWLInstance (s + 1) G₀ G₁)
            (C * (s * 2 ^ packedWidth x.length h s * (h + 1)) ^ c) := by
  obtain ⟨cp, hpack⟩ := packed_representation
  obtain ⟨compile, ⟨Cn, hgame⟩, ⟨Mc, -, Cc, cc, hMc⟩⟩ := matrix_compiler
  refine ⟨(cp + 2) * (cc + 1), Cn, fun M hM => ?_⟩
  obtain ⟨sys, Cs, hsys, Rp, -, hRp⟩ := hpack M hM
  obtain ⟨Kt, hKt⟩ : ∃ K, K = 2 * Cs + 16 * Cc * (21 * Cs + 7) ^ (cc + 1) + 16 * (5 + Cs) + 19 :=
    ⟨_, rfl⟩
  refine ⟨(Main.Compose.comp Rp (withLead Mc).compile false fun _ => false).toMachine,
    Main.AMachine.toMachine_deterministic _, Kt, 5 * Cs,
    fun x h s hx hh hxh hs hsh => ?_⟩
  have hℓ1 := one_le_packedWidth x.length h s
  have hQ := length_add_two_le x.length h s
  obtain ⟨hcorr, hloc, hsch⟩ := hsys x h s hx hh hxh hs hsh
  obtain ⟨Ck, hCk⟩ := hgame (s + 1) (by omega)
  obtain ⟨hsp, hdu, -, -, hlen⟩ := hCk _ hℓ1 (sys x h s)
  have hSz : matrixSize (sys x h s) ≤ 5 * (Cs * (h + 1) ^ 2) * (s + 1) ^ 2 *
      2 ^ packedWidth x.length h s * (packedWidth x.length h s + 1) :=
    (sizeParameter_le _).trans (size_arith hloc hsch)
  refine ⟨(compile (sys x h s)).1, (compile (sys x h s)).2, fun hhalt => ?_, ?_, ?_⟩
  · exact (hcorr hhalt).symm.trans (distinguishes_iff_conflict (by omega) _ hsp hdu).symm
  · rw [encodeWLInstance_eq, List.length_append]
    have h1 := length_encodeNat_le (s + 1)
    have h2 := hlen
    obtain ⟨Sb, hSb⟩ : ∃ Sb, Sb = 5 * Cs * (h + 1) ^ 2 * (s + 1) ^ 2 *
        2 ^ packedWidth x.length h s * (packedWidth x.length h s + 1) := ⟨_, rfl⟩
    rw [← hSb]
    have hS : matrixSize (sys x h s) ≤ Sb := hSz.trans_eq (by rw [hSb]; ring)
    have h3 : Cn * (matrixSize (sys x h s) + 1) *
        (Nat.log 2 (matrixSize (sys x h s) + 2) + 1) ≤ Cn * (Sb + 1) * (Nat.log 2 (Sb + 2) + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
        (by have := Nat.log_mono_right (b := 2) (show matrixSize (sys x h s) + 2 ≤ Sb + 2 by omega)
            omega)
    omega
  · have h1 := hRp x h s hx hh hxh hs hsh
    have h2 := hMc (s + 1) (by omega) _ hℓ1 (sys x h s)
    rw [encodeSystem_eq] at h2
    have h3 := withLead_computesWithin h2
    rw [← encodeSystem_eq, ← encodeWLInstance_eq] at h3
    have hxin2 : 2 ≤ (encodeNats [h, s] ++ x).length := by simp; omega
    have hc := Main.Compose.compose_computesWithin Rp (withLead Mc).compile false
      (fun _ => false) hxin2 h1 h3
    refine Main.Compose.computesWithin_mono' hc ?_
    obtain ⟨hX1, hX2, hX3, -⟩ := X_facts (h := h) (show 1 ≤ s by omega)
      (show 1 ≤ 2 ^ packedWidth x.length h s by omega)
    have hxin : (encodeNats [h, s] ++ x).length ≤
        5 * (s * 2 ^ packedWidth x.length h s * (h + 1)) := by
      have e1 := length_encodeNat_le h
      have e2 := length_encodeNat_le s
      simp only [encodeNats, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.length_append]
      omega
    have hH := length_le_of_computesWithin h1
    have hl : packedWidth x.length h s + 1 ≤ 2 ^ packedWidth x.length h s :=
      Nat.lt_two_pow_self
    have ht := time_arith (Cs := Cs) (Cc := Cc) (cp := cp) (cc := cc)
      (X := s * 2 ^ packedWidth x.length h s * (h + 1)) (by omega) hxin
      (T1_le (show 1 ≤ s by omega) (by omega)) hH (S_le hSz hl (by omega)) T2_le
    rw [← hKt] at ht
    exact ht

end Lax119563Proofs.Hardness

end Hardness_PipelineLen

/-! ### Formerly `Lax119563Proofs.Hardness.SuffixMachine` -/

section Hardness_SuffixMachine

/-!
# Keeping the input behind the output

For a deterministic machine `D`, the machine `(withSuffix D).compile` copies its input `x` to
a separate tape, runs `D` on `x` (by `simTM`), and then appends `x` to the output of `D`. So
if `D` computes `z` from `x` within `t` steps, it computes `z ++ x` within
`16 (t + |x| + |z| + 1)` steps (`withSuffix_computesWithin`).
-/

open Lax489179.TuringMachine (Machine Config Move Instruction init step run Deterministic)
open Lax119563.DeterministicTime Lax119563.BinaryEncodings

namespace Lax119563Proofs.Hardness

open Machines Machines.TM Function

variable (D : Machine)

/-- The machine appending the input to the output of `D`. -/
noncomputable def withSuffix : TM (D.tapes + 3 + 1) (Fin (D.symbols + 3)) :=
  copyR 0 (iP D) (nb D) ;; rewind 0 ;; rewind (iP D) ;; write (iM D) (mark D) ;;
    onTapes (σL D) (simTM D) ;; scanR 0 (nb D) ;; copyR (iP D) 0 (nb D)

variable {D}

/-- **Specification of `withSuffix`** on structured tapes. -/
theorem withSuffix_runsWithin {x z : List Bool} {t : ℕ} (hD : ComputesWithin D x z t) :
    ∃ T', (withSuffix D).RunsWithin (inputTapes (D.tapes + 3) x)
      (2 * t + 8 * x.length + 2 * z.length + 6) T' ∧
      T' 0 = Tape.ofWord (bitsWord (z ++ x)) [] := by
  set X : List (Fin (D.symbols + 3)) := bitsWord x with hX
  set Z : List (Fin (D.symbols + 3)) := bitsWord z with hZ
  set T0 := inputTapes (Γ := Fin (D.symbols + 3)) (D.tapes + 3) x with hT0
  have hT00 : T0 0 = .ofWord [] (X ++ []) := by
    rw [hT0, inputTapes_zero]; simp [hX, bitsWord]
  have hT0x : ∀ y : Fin (D.tapes + 4), y ≠ 0 → T0 y = .ofWord [] [] :=
    fun y hy => inputTapes_ne_zero _ hy
  -- 1. copy the input
  obtain ⟨T1, h1, f1a, f1b, f1c⟩ : ∃ T1, (copyR 0 (iP D) (nb D)).RunsWithin T0
      (2 * X.length) T1 ∧ T1 0 = .ofWord X [] ∧ T1 (iP D) = .ofWord X [] ∧
      ∀ y, y ≠ 0 → y ≠ iP D → T1 y = T0 y :=
    ⟨_, copyR_ofWord (iP_ne_zero (D := D)).symm (nb D) (pre := []) (u := X) (rest := [])
      (dpre := []) (drest := []) hT00 (nb_bitsWord _) (by simp [nb]) (hT0x _ iP_ne_zero),
      by simp [update_of_ne (iP_ne_zero (D := D)).symm],
      by simp,
      fun y h0 hP => by simp [update_of_ne h0, update_of_ne hP]⟩
  -- 2. rewind tape 0
  obtain ⟨T2, h2, f2a, f2c⟩ : ∃ T2, (rewind 0).RunsWithin T1 (2 * X.length + 2) T2 ∧
      T2 0 = .ofWord [] X ∧ ∀ y, y ≠ 0 → T2 y = T1 y :=
    ⟨_, rewind_ofWord 0 f1a (ne_blank_bitsWord _), by simp,
      fun y h0 => by simp [update_of_ne h0]⟩
  -- 3. rewind the copy
  obtain ⟨T3, h3, f3a, f3b, f3c⟩ : ∃ T3, (rewind (iP D)).RunsWithin T2 (2 * X.length + 2) T3 ∧
      T3 0 = .ofWord [] X ∧ T3 (iP D) = .ofWord [] X ∧
      ∀ y, y ≠ 0 → y ≠ iP D → T3 y = T0 y :=
    ⟨_, rewind_ofWord (iP D) (by rw [f2c _ iP_ne_zero, f1b]) (ne_blank_bitsWord _),
      by simp [update_of_ne (iP_ne_zero (D := D)).symm, f2a], by simp,
      fun y h0 hP => by simp [update_of_ne hP, f2c _ h0, f1c _ h0 hP]⟩
  -- 4. mark the origin
  obtain ⟨T4, h4, f4a, f4b, f4m, f4c⟩ : ∃ T4, (write (iM D) (mark D)).RunsWithin T3 1 T4 ∧
      T4 0 = .ofWord [] X ∧ T4 (iP D) = .ofWord [] X ∧ T4 (iM D) = .ofWord [] [mark D] ∧
      ∀ y, y ≠ 0 → y ≠ iP D → y ≠ iM D → T4 y = T0 y :=
    ⟨_, write_runsWithin _ _ _, by simp [update_of_ne (iM_ne_zero (D := D)).symm, f3a],
      by simp [update_of_ne (iP_ne_iM (D := D)), f3b],
      by simp [f3c _ iM_ne_zero iP_ne_iM.symm, hT0x _ iM_ne_zero, Tape.act_ofWord_stay],
      fun y h0 hP hM => by simp [update_of_ne hM, f3c _ h0 hP]⟩
  -- 5. simulate `D`
  have hsim := simTM_runsWithin hD (T := T4 ∘ σL D)
    (fun j => by
      show T4 (σL D j.castSucc) = _
      rw [init_tape]
      by_cases hj : j = 0
      · subst hj
        rw [Fin.castSucc_zero, σL_zero, f4a, inputTapes_zero]
        exact Tape.ext (by simp) (by simp [hX, bitsWord])
      · have h0 : σL D j.castSucc ≠ 0 := by
          intro h; apply hj; ext; have := congrArg Fin.val h; simpa [σL] using this
        rw [f4c _ h0 (σL_ne_iP _) (σL_castSucc_ne_iM _), hT0x _ h0, inputTapes_ne_zero _ hj]
        rfl)
    (by show T4 (σL D (mkI D)) = _; rw [σL_mkI, f4m]; rfl)
  obtain ⟨T', h5', hT'0⟩ := hsim
  have h5 := onTapes_runsWithin (σL D) h5'
  obtain ⟨T5, h5, f5a, f5b⟩ : ∃ T5, (onTapes (σL D) (simTM D)).RunsWithin T4 (2 * t) T5 ∧
      T5 0 = .ofWord [] Z ∧ T5 (iP D) = .ofWord [] X :=
    ⟨_, h5, by rw [← σL_zero, updateTapes_apply_self, hT'0],
      by rw [updateTapes_apply_of_not_mem _ _ _ σL_ne_iP, f4b]⟩
  -- 6. move to the end of the output
  obtain ⟨T6, h6, f6a, f6b⟩ : ∃ T6, (scanR 0 (nb D)).RunsWithin T5 (2 * Z.length) T6 ∧
      T6 0 = .ofWord Z [] ∧ T6 (iP D) = .ofWord [] X :=
    ⟨_, scanR_ofWord 0 (nb D) (pre := []) (u := Z) (rest := []) (by simpa using f5a)
      (nb_bitsWord _) (by simp [nb]), by simp,
      by simp [update_of_ne (iP_ne_zero (D := D)), f5b]⟩
  -- 8. append the input
  obtain ⟨T8, h8, f8a⟩ : ∃ T8, (copyR (iP D) 0 (nb D)).RunsWithin T6 (2 * X.length) T8 ∧
      T8 0 = .ofWord (Z ++ X) [] :=
    ⟨_, copyR_ofWord (iP_ne_zero (D := D)) (nb D) (pre := []) (u := X) (rest := [])
      (dpre := Z) (drest := []) (by simpa using f6b) (nb_bitsWord _) (by simp [nb]) f6a,
      by simp⟩
  have h := seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin
    (seq_runsWithin h1 h2) h3) h4) h5) h6) h8
  refine ⟨T8, h.mono ?_, by rw [f8a]; simp [hX, hZ, bitsWord]⟩
  have hXl : X.length = x.length := by simp [hX, bitsWord]
  have hZl : Z.length = z.length := by simp [hZ, bitsWord]
  omega

/-- **Keeping the input behind the output.** -/
theorem withSuffix_computesWithin {x z : List Bool} {t : ℕ} (hD : ComputesWithin D x z t) :
    ComputesWithin (withSuffix D).compile x (z ++ x) (16 * (t + x.length + 1)) := by
  obtain ⟨T', h, hT'⟩ := withSuffix_runsWithin hD
  have hc := (withSuffix D).computesWithin (fun _ _ => false) h
    (y := z ++ x) (by rw [hT']; simp [bitsWord])
  have hz := length_le_of_computesWithin hD
  refine Main.Compose.computesWithin_mono' hc ?_
  omega

theorem withSuffix_deterministic : Deterministic (withSuffix D).compile :=
  (withSuffix D).deterministic_compile

end Lax119563Proofs.Hardness

end Hardness_SuffixMachine

/-! ### Formerly `Lax119563Proofs.Hardness.XpMachine` -/

section Hardness_XpMachine

/-!
# Padding the input and running a machine on it

For a deterministic machine `D`, the machine `(padTM D).compile` writes
`true :: true :: x` from its input `x` and runs `D` on it (by `simTM`). So if `D` computes `z`
from `true :: true :: x` within `t` steps, `padTM D` computes `z` from `x` within
`20 |x| + 41 + 2 t` steps (`padTM_computesWithin`). This removes the restriction to inputs of
length at least `2` of the composition of machines (`Main.Compose.compose_computesWithin`):
`D` is a composition, run on padded inputs.
-/

open Lax489179.TuringMachine (Machine Config Move Instruction init step run Deterministic)
open Lax119563.DeterministicTime Lax119563.BinaryEncodings

namespace Lax119563Proofs.Hardness

open Machines Machines.TM Function

section Pad

variable (D : Machine)

/-- The machine writing `true :: true :: x` and running `D` on it. -/
noncomputable def padTM : TM (D.tapes + 3 + 1) (Fin (D.symbols + 3)) :=
  writeR (iB D) (bit true) ;; writeR (iB D) (bit true) ;; copyR 0 (iB D) (nb D) ;;
    erase 0 ;; rewind (iB D) ;; copyR (iB D) 0 (nb D) ;; rewind 0 ;;
    write (iM D) (mark D) ;; onTapes (σL D) (simTM D)

theorem padTM_deterministic : Deterministic (padTM D).compile :=
  (padTM D).deterministic_compile

variable {D}

/-- **Specification of `padTM`.** -/
theorem padTM_runsWithin {x z : List Bool} {t : ℕ}
    (hD : ComputesWithin D (true :: true :: x) z t) :
    ∃ T', (padTM D).RunsWithin (inputTapes (D.tapes + 3) x) (20 * x.length + 40 + 2 * t) T' ∧
      T' 0 = Tape.ofWord [] (bitsWord z) := by
  set X : List (Fin (D.symbols + 3)) := bitsWord x with hX
  set Y : List (Fin (D.symbols + 3)) := bitsWord (true :: true :: x) with hY
  set e₀ : Machines.Tape (Fin (D.symbols + 3)) := .ofWord [] [] with he₀
  have hXb : ∀ a ∈ X, a ≠ blank := fun a ha => bit_ne_blank_of_mem_bitsWord ha
  have hYb : ∀ a ∈ Y, a ≠ blank := fun a ha => bit_ne_blank_of_mem_bitsWord ha
  have hYeq : Y = [bit true, bit true] ++ X := by simp [hY, hX, bitsWord]
  have hXl : X.length = x.length := by simp [hX, bitsWord]
  -- 1., 2. the padding
  have h1 := writeR_runsWithin (iB D) (bit true) (St (.ofWord [] X) e₀ e₀ e₀)
  simp only [St_iB, he₀, Tape.act_ofWord_right, List.tail_nil, update_St_iB,
    List.nil_append] at h1
  have h2 := writeR_runsWithin (iB D) (bit true) (St (.ofWord [] X) e₀
    (.ofWord [bit true] []) e₀)
  simp only [St_iB, Tape.act_ofWord_right, List.tail_nil, update_St_iB,
    List.singleton_append] at h2
  -- 3. copy the input
  have h3 := copyR_ofWord (iB_ne_zero (D := D)).symm (nb D) (pre := []) (u := X) (rest := [])
    (T := St (.ofWord [] X) e₀ (.ofWord [bit true, bit true] []) e₀)
    (dpre := [bit true, bit true]) (drest := []) (by simp)
    (fun a ha => by simpa [nb] using hXb a ha) (by simp [nb]) (by simp)
  simp only [update_St_zero, update_St_iB, List.nil_append, List.drop_nil] at h3
  rw [show [bit true, bit true] ++ X = Y by rw [hYeq]] at h3
  -- 4. erase tape 0
  have h4 := erase_ofWord 0 (T := St (.ofWord X []) e₀ (.ofWord Y []) e₀)
    (pre := X) (rest := []) (by simp) (by simpa using hXb)
  simp only [update_St_zero] at h4
  -- 5. rewind the buffer
  have h5 := rewind_ofWord (iB D) (T := St (.ofWord [] []) e₀ (.ofWord Y []) e₀)
    (pre := Y) (rest := []) (by simp) hYb
  simp only [update_St_iB, List.append_nil] at h5
  -- 6. copy back
  have h6 := copyR_ofWord (iB_ne_zero (D := D)) (nb D) (pre := []) (u := Y) (rest := [])
    (T := St (.ofWord [] []) e₀ (.ofWord [] Y) e₀)
    (dpre := []) (drest := []) (by simp)
    (fun a ha => by simpa [nb] using hYb a ha) (by simp [nb]) (by simp)
  simp only [update_St_zero, update_St_iB, List.nil_append, List.drop_nil] at h6
  -- 7. rewind tape 0
  have h7 := rewind_ofWord 0 (T := St (.ofWord Y []) e₀ (.ofWord Y []) e₀)
    (pre := Y) (rest := []) (by simp) hYb
  simp only [update_St_zero, List.append_nil] at h7
  -- 8. the mark
  have h8 := write_runsWithin (iM D) (mark D) (St (.ofWord [] Y) e₀ (.ofWord Y []) e₀)
  simp only [St_iM, he₀, Tape.act_ofWord_stay, List.tail_nil, update_St_iM] at h8
  -- 9. simulate `D`
  set T8 := St (.ofWord [] Y) e₀ (.ofWord Y []) (.ofWord [] [mark D]) with hT8
  have hsim := simTM_runsWithin hD (T := T8 ∘ σL D)
    (fun j => by
      show T8 (σL D j.castSucc) = _
      rw [init_tape]
      by_cases hj : j = 0
      · subst hj
        rw [Fin.castSucc_zero, σL_zero, hT8, St_zero, inputTapes_zero]
        exact Tape.ext (by simp) (by simp [hY, bitsWord])
      · have h0 : σL D j.castSucc ≠ 0 := by
          intro h; apply hj; ext; have := congrArg Fin.val h; simpa [σL] using this
        rw [hT8, St_other _ _ _ _ h0 (σL_ne_iP _) (σL_ne_iB _) (σL_castSucc_ne_iM _),
          inputTapes_ne_zero _ hj]
        rfl)
    (by show T8 (σL D (mkI D)) = _; rw [σL_mkI, hT8, St_iM]; rfl)
  obtain ⟨T', h9', hT'0⟩ := hsim
  have h9 := onTapes_runsWithin (σL D) h9'
  have h := seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin (seq_runsWithin
    (seq_runsWithin (seq_runsWithin (seq_runsWithin h1 h2) h3) h4) h5) h6) h7) h8) h9
  rw [inputTapes_eq_St]
  refine ⟨_, h.mono ?_, by rw [← σL_zero, updateTapes_apply_self, hT'0]⟩
  have hYl : Y.length = x.length + 2 := by simp [hY, bitsWord]
  simp only [List.length_nil, List.append_nil, hYl, hXl]
  omega

/-- **Padding and running.** -/
theorem padTM_computesWithin {x z : List Bool} {t : ℕ}
    (hD : ComputesWithin D (true :: true :: x) z t) :
    ComputesWithin (padTM D).compile x z (20 * x.length + 41 + 2 * t) := by
  obtain ⟨T', hrun, hT'⟩ := padTM_runsWithin hD
  have hcw := (padTM D).computesWithin (fun _ _ => false) hrun (y := z)
    (by rw [hT']; simp [Machines.bitsWord])
  exact Main.Compose.computesWithin_mono' hcw (by omega)

end Pad

end Lax119563Proofs.Hardness

end Hardness_XpMachine

/-! ### Formerly `Lax119563Proofs.Reduction.Bits` -/

section Reduction_Bits

/-!
# Little-endian digit lists

Facts about `Nat.bits` used by the arithmetic routines of register machines on stacks
(`Reduction.HStack`): canonical digit lists, ripple-carry addition (`addL`), and comparison
by a scan from the least significant digit (`cmpL`).
-/

namespace Lax119563Proofs.Reduction

open Machines (valBits valBits_bits bits_injective)

/-- A digit list without trailing (most significant) zeros. -/
def Canon : List Bool → Prop
  | [] => True
  | b :: l => (l = [] → b = true) ∧ Canon l

lemma valBits_ne_zero : ∀ {l : List Bool}, Canon l → l ≠ [] → valBits l ≠ 0
  | [], _, h => absurd rfl h
  | b :: l, ⟨h1, h2⟩, _ => by
    by_cases hl : l = []
    · subst hl; simp [h1 rfl, valBits]
    · have := valBits_ne_zero h2 hl
      simp only [valBits]; omega

lemma bits_valBits : ∀ {l : List Bool}, Canon l → Nat.bits (valBits l) = l
  | [], _ => by simp [valBits]
  | b :: l, ⟨h1, h2⟩ => by
    by_cases hl : l = []
    · subst hl; rw [h1 rfl]; simp [valBits]
    · have hv := valBits_ne_zero h2 hl
      have ih := bits_valBits h2
      cases b
      · simp only [valBits, Bool.toNat_false, zero_add]
        rw [Nat.bit0_bits _ hv, ih]
      · simp only [valBits, Bool.toNat_true]
        rw [add_comm, Nat.bit1_bits, ih]

lemma canon_bits (n : ℕ) : Canon (Nat.bits n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [Canon]
      · rw [Nat.bit0_bits m (by omega)]
        refine ⟨fun h => ?_, ih m (by omega)⟩
        exact absurd h (by rw [Machines.bits_eq_nil_iff]; omega)
    · rw [Nat.bit1_bits]
      exact ⟨fun _ => rfl, ih m (by omega)⟩

lemma bits_eq_of_canon {l : List Bool} (h : Canon l) {n : ℕ} (hv : valBits l = n) :
    Nat.bits n = l := hv ▸ bits_valBits h

lemma length_bits_le {n w : ℕ} (h : n < 2 ^ w) : (Nat.bits n).length ≤ w := by
  induction w generalizing n with
  | zero =>
    have : n = 0 := by simpa using h
    subst this; simp
  | succ w ih =>
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      · rw [Nat.bit0_bits m (by omega)]
        simp only [List.length_cons, add_le_add_iff_right]
        exact ih (by rw [pow_succ] at h; omega)
    · rw [Nat.bit1_bits]
      simp only [List.length_cons, add_le_add_iff_right]
      exact ih (by rw [pow_succ] at h; omega)

/-! ## Addition -/

/-- The carry of a full adder. -/
def maj (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

/-- Ripple-carry addition of digit lists with carry `c`. -/
def addL : List Bool → List Bool → Bool → List Bool
  | [], [], c => if c then [true] else []
  | a :: l, [], c => Bool.xor a c :: addL l [] (a && c)
  | [], b :: l', c => Bool.xor b c :: addL [] l' (b && c)
  | a :: l, b :: l', c => Bool.xor (Bool.xor a b) c :: addL l l' (maj a b c)

lemma valBits_addL : ∀ (l l' : List Bool) (c : Bool),
    valBits (addL l l' c) = valBits l + valBits l' + c.toNat
  | [], [], c => by cases c <;> simp [addL, valBits]
  | a :: l, [], c => by
    rw [addL]; simp only [valBits]; rw [valBits_addL l [] _]; cases a <;> cases c <;> simp [valBits] <;> omega
  | [], b :: l, c => by
    rw [addL]; simp only [valBits]; rw [valBits_addL [] l _]; cases b <;> cases c <;> simp [valBits] <;> omega
  | a :: l, b :: l', c => by
    rw [addL]; simp only [valBits]; rw [valBits_addL l l' _]
    cases a <;> cases b <;> cases c <;> simp [maj] <;> omega

lemma addL_eq_nil {l l' : List Bool} {c : Bool} (h : addL l l' c = []) :
    l = [] ∧ l' = [] ∧ c = false := by
  cases l <;> cases l' <;> cases c <;> simp_all [addL]

lemma canon_addL : ∀ (l l' : List Bool) (c : Bool), Canon l → Canon l' → Canon (addL l l' c)
  | [], [], c, _, _ => by cases c <;> simp [addL, Canon]
  | a :: l, [], c, hl, hl' => by
    rw [addL]
    refine ⟨fun he => ?_, canon_addL l [] _ hl.2 hl'⟩
    obtain ⟨rfl, -, h⟩ := addL_eq_nil he
    have := hl.1 rfl; subst this; cases c <;> simp_all
  | [], b :: l, c, hl, hl' => by
    rw [addL]
    refine ⟨fun he => ?_, canon_addL [] l _ hl hl'.2⟩
    obtain ⟨-, rfl, h⟩ := addL_eq_nil he
    have := hl'.1 rfl; subst this; cases c <;> simp_all
  | a :: l, b :: l', c, hl, hl' => by
    rw [addL]
    refine ⟨fun he => ?_, canon_addL l l' _ hl.2 hl'.2⟩
    obtain ⟨rfl, rfl, h⟩ := addL_eq_nil he
    have := hl.1 rfl; have := hl'.1 rfl; subst_vars; cases c <;> simp_all [maj]

/-- `Nat.bits` of a sum. -/
lemma bits_add (a b : ℕ) : Nat.bits (a + b) = addL (Nat.bits a) (Nat.bits b) false := by
  refine bits_eq_of_canon (canon_addL _ _ _ (canon_bits a) (canon_bits b)) ?_
  rw [valBits_addL, valBits_bits, valBits_bits]; simp

/-! ## Comparison -/

/-- Comparison of digit lists by a scan from the least significant digit; `st` is the result
for the digits seen so far. -/
def cmpL : List Bool → List Bool → Ordering → Ordering
  | [], [], st => st
  | a :: l, [], st => cmpL l [] ((compare a false).then st)
  | [], b :: l', st => cmpL [] l' ((compare false b).then st)
  | a :: l, b :: l', st => cmpL l l' ((compare a b).then st)

lemma compare_bit_add (a b : Bool) (x y : ℕ) :
    compare (a.toNat + 2 * x) (b.toNat + 2 * y) = (compare x y).then (compare a b) := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · rw [compare_lt_iff_lt.mpr hxy,
      compare_lt_iff_lt.mpr (by cases a <;> cases b <;> simp <;> omega)]
    rfl
  · cases a <;> cases b <;> simp [compare, compareOfLessAndEq]
  · rw [compare_gt_iff_gt.mpr hxy,
      compare_gt_iff_gt.mpr (by cases a <;> cases b <;> simp <;> omega)]
    rfl

lemma cmpL_spec : ∀ (l l' : List Bool) (st : Ordering),
    cmpL l l' st = (compare (valBits l) (valBits l')).then st
  | [], [], st => by simp [cmpL, valBits]
  | a :: l, [], st => by
    rw [cmpL, cmpL_spec l [] _, ← Ordering.then_assoc]
    have := compare_bit_add a false (valBits l) 0
    simp only [valBits, Bool.toNat_false, mul_zero, add_zero] at this ⊢
    rw [this]
  | [], b :: l, st => by
    rw [cmpL, cmpL_spec [] l _, ← Ordering.then_assoc]
    have := compare_bit_add false b 0 (valBits l)
    simp only [valBits, Bool.toNat_false, mul_zero, zero_add] at this ⊢
    rw [this]
  | a :: l, b :: l', st => by
    rw [cmpL, cmpL_spec l l' _, ← Ordering.then_assoc]; simp only [valBits]; rw [compare_bit_add]

/-- The value read from the remaining input: `0` at its end, else the next bit plus one. -/
def rdVal : List Bool → ℕ
  | [] => 0
  | b :: _ => b.toNat + 1

end Lax119563Proofs.Reduction

end Reduction_Bits

/-! ### Formerly `Lax119563Proofs.Reduction.CountIdx` -/

section Reduction_CountIdx

/-!
# The lexicographic order on keys

`lexLt`: the strict lexicographic order on pairs of numbers (irreflexive and asymmetric), used
for the keys of the command and schema stacks.
-/

namespace Lax119563Proofs.Reduction

variable {α : Type*}

/-- Lexicographic order on pairs of naturals, as a Boolean. -/
def lexLt (p q : ℕ × ℕ) : Bool := decide (p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2))

lemma lexLt_irrefl (p : ℕ × ℕ) : lexLt p p = false := by
  simp [lexLt]

lemma lexLt_asymm {p q : ℕ × ℕ} (h : lexLt p q = true) : lexLt q p = false := by
  simp only [lexLt, decide_eq_true_eq, decide_eq_false_iff_not] at *
  omega

end Lax119563Proofs.Reduction

end Reduction_CountIdx

/-! ### Formerly `Lax119563Proofs.Reduction.HProg` -/

section Reduction_HProg

/-!
# Register programs with binary registers

A small structured programming language for writing the reduction machine. A program has
registers `Fin R` holding natural numbers, reads its input `x` through a cursor `pos`, and
emits natural numbers; the output of a run is the list `out` of emitted numbers, which the
compiled machine writes as `encodeNats out`.

Instructions: `clr r` (`r := 0`), `one r` (`r := 2r + 1`), `dbl r` (`r := 2r`), `half r`
(`r := r / 2`), `copy r s` (`s := r`), `add r s` (`r := r + s`), `lt f a b`
(`f := [a < b]`), `emit r`, `rd r` (`r := x[pos] + 1`, or `0` at the end of the input;
advance the cursor), `rst` (cursor back to `0`), and sequencing, conditionals and while
loops whose conditions inspect, for every register, whether it is zero and its parity.

The big-step semantics `HRuns x w p st st' t` fixes a *word size* `w`: every primitive
instruction requires the registers it touches to stay below `2 ^ w` and costs
`unitCost w = 64 (w + 1)` (`rst` costs `unitCost w * (pos + 1)`); control costs one unit per
test. The compiled stack program (`Reduction.HCompile`) runs within the same cost.
-/

open Lax119563.BinaryEncodings

namespace Lax119563Proofs.Reduction

/-- The view of a register used by conditions: `none` for `0`, else `some` of its parity. -/
abbrev RView (R : ℕ) := Fin R → Option Bool

/-- Programs over registers `Fin R`. -/
inductive HProg (R : ℕ) where
  | clr (r : Fin R)
  | one (r : Fin R)
  | dbl (r : Fin R)
  | half (r : Fin R)
  | copy (r s : Fin R)
  | add (r s : Fin R)
  | lt (f a b : Fin R)
  | emit (r : Fin R)
  | rd (r : Fin R)
  | rst
  | seq (p q : HProg R)
  | ite (c : RView R → Bool) (p q : HProg R)
  | loop (c : RView R → Bool) (p : HProg R)

/-- States: registers, input cursor, emitted numbers. -/
@[ext]
structure HSt (R : ℕ) where
  env : Fin R → ℕ
  pos : ℕ
  out : List ℕ

namespace HSt

variable {R : ℕ}

/-- The view of the registers. -/
def view (st : HSt R) : RView R := fun r => if st.env r = 0 then none else some (st.env r % 2 == 1)

/-- Set a register. -/
def set (st : HSt R) (r : Fin R) (v : ℕ) : HSt R := { st with env := Function.update st.env r v }

@[simp] lemma set_env (st : HSt R) (r : Fin R) (v : ℕ) :
    (st.set r v).env = Function.update st.env r v := rfl
@[simp] lemma set_pos (st : HSt R) (r : Fin R) (v : ℕ) : (st.set r v).pos = st.pos := rfl
@[simp] lemma set_out (st : HSt R) (r : Fin R) (v : ℕ) : (st.set r v).out = st.out := rfl

end HSt

/-- The cost of a primitive instruction for word size `w`. -/
def unitCost (w : ℕ) : ℕ := 64 * (w + 1)

/-- The value read at cursor position `pos`. -/
def inBit (x : List Bool) (pos : ℕ) : ℕ := rdVal (x.drop pos)

variable {R : ℕ}

/-- Big-step semantics with word size `w` on input `x`. -/
inductive HRuns (x : List Bool) (w : ℕ) : HProg R → HSt R → HSt R → ℕ → Prop
  | clr {r st} : st.env r < 2 ^ w → HRuns x w (.clr r) st (st.set r 0) (unitCost w)
  | one {r st} : 2 * st.env r + 1 < 2 ^ w →
      HRuns x w (.one r) st (st.set r (2 * st.env r + 1)) (unitCost w)
  | dbl {r st} : 2 * st.env r < 2 ^ w → HRuns x w (.dbl r) st (st.set r (2 * st.env r)) (unitCost w)
  | half {r st} : st.env r < 2 ^ w → HRuns x w (.half r) st (st.set r (st.env r / 2)) (unitCost w)
  | copy {r s st} : r ≠ s → st.env r < 2 ^ w → st.env s < 2 ^ w →
      HRuns x w (.copy r s) st (st.set s (st.env r)) (unitCost w)
  | add {r s st} : r ≠ s → st.env r + st.env s < 2 ^ w →
      HRuns x w (.add r s) st (st.set r (st.env r + st.env s)) (unitCost w)
  | lt {f a b st} : f ≠ a → f ≠ b → a ≠ b → st.env f < 2 ^ w → st.env a < 2 ^ w →
      st.env b < 2 ^ w →
      HRuns x w (.lt f a b) st (st.set f (if st.env a < st.env b then 1 else 0)) (unitCost w)
  | emit {r st} : st.env r < 2 ^ w →
      HRuns x w (.emit r) st { st with out := st.out ++ [st.env r] } (unitCost w)
  | rd {r st} : st.env r < 2 ^ w → st.pos ≤ x.length →
      HRuns x w (.rd r) st
        { (st.set r (inBit x st.pos)) with pos := min (st.pos + 1) x.length } (unitCost w)
  | rst {st} : st.pos ≤ x.length →
      HRuns x w .rst st { st with pos := 0 } (unitCost w * (st.pos + 1))
  | seq {p q st₁ st₂ st₃ t₁ t₂} : HRuns x w p st₁ st₂ t₁ → HRuns x w q st₂ st₃ t₂ →
      HRuns x w (.seq p q) st₁ st₃ (t₁ + t₂)
  | iteT {c p q st st' t} : c st.view = true → HRuns x w p st st' t →
      HRuns x w (.ite c p q) st st' (t + 1)
  | iteF {c p q st st' t} : c st.view = false → HRuns x w q st st' t →
      HRuns x w (.ite c p q) st st' (t + 1)
  | loopF {c p st} : c st.view = false → HRuns x w (.loop c p) st st 1
  | loopT {c p st₁ st₂ st₃ t₁ t₂} : c st₁.view = true → HRuns x w p st₁ st₂ t₁ →
      HRuns x w (.loop c p) st₂ st₃ t₂ → HRuns x w (.loop c p) st₁ st₃ (t₁ + t₂ + 1)

/-- The cursor stays within the input. -/
lemma HRuns.pos_le {x : List Bool} {w : ℕ} {p : HProg R} {st st' : HSt R} {t : ℕ}
    (h : HRuns x w p st st' t) (hp : st.pos ≤ x.length) : st'.pos ≤ x.length := by
  induction h with
  | rd => simp
  | rst => simp
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hp)
  | iteT _ _ ih => exact ih hp
  | iteF _ _ ih => exact ih hp
  | loopF => exact hp
  | loopT _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hp)
  | _ => simpa using hp

end Lax119563Proofs.Reduction

end Reduction_HProg

/-! ### Formerly `Lax119563Proofs.Reduction.HStack` -/

section Reduction_HStack

/-!
# Binary registers on stacks

Stack programs over the symbols `Fin 2` (`m = 0`) implementing the primitive instructions of
`HProg` on numbers stored as their binary digits, least significant digit on top
(`nst v = (Nat.bits v).map sym`). Every routine is specified for arbitrary stacks: it changes
only the stacks named in its conclusion and restores its empty helper stacks.
-/

open Function

namespace Lax119563Proofs.Reduction

open Hierarchy Hierarchy.Prog
open Machines (valBits valBits_bits)

/-- Stack symbols. -/
abbrev Sym := Fin (0 + 2)

/-- A bit as a stack symbol. -/
def sym (b : Bool) : Sym := if b then 1 else 0

@[simp] lemma sym_true : sym true = 1 := rfl
@[simp] lemma sym_false : sym false = 0 := rfl

/-- A list of bits as stack symbols. -/
def bs (l : List Bool) : List Sym := l.map sym

/-- The stack of a number: its binary digits, least significant on top. -/
def nst (v : ℕ) : List Sym := bs (Nat.bits v)

@[simp] lemma bs_nil : bs [] = [] := rfl
@[simp] lemma bs_cons (b : Bool) (l : List Bool) : bs (b :: l) = sym b :: bs l := rfl
@[simp] lemma length_bs (l : List Bool) : (bs l).length = l.length := List.length_map _
lemma bs_append (l l' : List Bool) : bs (l ++ l') = bs l ++ bs l' := List.map_append
lemma bs_reverse (l : List Bool) : bs l.reverse = (bs l).reverse := List.map_reverse ..

@[simp] lemma nst_zero : nst 0 = [] := by simp [nst]

lemma nst_bit1 (v : ℕ) : nst (2 * v + 1) = 1 :: nst v := by simp [nst, Nat.bit1_bits]

lemma nst_bit0 {v : ℕ} (hv : v ≠ 0) : nst (2 * v) = 0 :: nst v := by
  simp [nst, Nat.bit0_bits v hv]

lemma bits_div_two (v : ℕ) : Nat.bits (v / 2) = (Nat.bits v).tail := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' v
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [Nat.bit0_bits m (by omega)]; simp
  · rw [show (2 * m + 1) / 2 = m by omega, Nat.bit1_bits]; simp

lemma nst_half (v : ℕ) : nst (v / 2) = (nst v).tail := by
  simp [nst, bs, bits_div_two, List.map_tail]

lemma length_nst_le {v w : ℕ} (h : v < 2 ^ w) : (nst v).length ≤ w := by
  simpa [nst] using length_bits_le h

lemma nst_eq_nil_iff (v : ℕ) : nst v = [] ↔ v = 0 := by
  simp [nst, bs, Machines.bits_eq_nil_iff]

lemma head_nst (v : ℕ) :
    ((nst v).head?.map (· == 1)) = if v = 0 then none else some (v % 2 == 1) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' v
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [nst_bit0 (by omega)]; simp; omega
  · rw [nst_bit1]; simp

variable {K : ℕ}

/-! ## Single instructions -/

/-- `r := 2r + 1`. -/
def hOne (r : Fin K) : Prog K 0 := push r 1

lemma hOne_runs (r : Fin K) {s : Stacks K 0} {v : ℕ} (hs : s r = nst v) :
    (hOne r).RunsLe s (update s r (nst (2 * v + 1))) 2 :=
  (RunsLe.push r 1 s).of_eq (by rw [hs, nst_bit1]) le_rfl

/-- `r := 2r`. -/
def hDbl (r : Fin K) : Prog K 0 := ite (fun t => (t r).isSome) (push r 0) skip

lemma hDbl_runs (r : Fin K) {s : Stacks K 0} {v : ℕ} (hs : s r = nst v) :
    (hDbl r).RunsLe s (update s r (nst (2 * v))) 3 := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · refine ((RunsLe.skip s).iteF (by simp [tops, hs])).of_eq ?_ (by norm_num)
    simp only [mul_zero]; rw [← hs]; simp
  · refine ((RunsLe.push r 0 s).iteT ?_).of_eq ?_ le_rfl
    · have : nst v ≠ [] := by rw [Ne, nst_eq_nil_iff]; omega
      simp [tops, hs, Option.isSome_iff_ne_none, List.head?_eq_none_iff, this]
    · rw [hs, nst_bit0 (by omega)]

/-- `r := r / 2`. -/
def hHalf (r : Fin K) : Prog K 0 := pop r

lemma hHalf_runs (r : Fin K) {s : Stacks K 0} {v : ℕ} (hs : s r = nst v) :
    (hHalf r).RunsLe s (update s r (nst (v / 2))) 1 :=
  (RunsLe.pop r s).of_eq (by rw [hs, nst_half]) le_rfl

lemma clear_nst (r : Fin K) {s : Stacks K 0} {v : ℕ} (hs : s r = nst v) :
    (clear r).RunsLe s (update s r (nst 0)) (2 * (nst v).length + 1) :=
  (clear_runs r _ s hs).of_eq (by simp) le_rfl

/-! ## Copying -/

/-- `d := r` through the empty helper `t`. -/
def hCopy (r d t : Fin K) : Prog K 0 := seq (clear d) (seq (moveAll r t) (dupAll t r d))

lemma hCopy_runs {r d t : Fin K} (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t) {s : Stacks K 0}
    {v : ℕ} (hs : s r = nst v) (ht : s t = []) :
    (hCopy r d t).RunsLe s (update s d (nst v))
      (2 * (s d).length + 16 * (nst v).length + 3) := by
  have h1 := clear_runs d (s d) s rfl
  have h2 := moveAll_runs hrt (nst v) (update s d []) (by simp [update_of_ne hrd, hs])
  have h3 := dupAll_runs hrt.symm hdt.symm hrd (m := 0) ((nst v).reverse)
    (update (update (update s d []) r []) t ((nst v).reverse ++ update s d [] t))
    (by simp [update_of_ne hdt.symm, ht])
  refine (h1.seq (h2.seq h3)).of_eq ?_ (by simp; omega)
  funext k
  simp only [update_apply]
  split_ifs <;> simp_all

/-- `d := r` for an empty `d`, leaving the copy reversed on nothing: copy `r` onto the empty
helper `d` through `t` (`d` must be empty). -/
lemma hCopy_runs_empty {r d t : Fin K} (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t)
    {s : Stacks K 0} {v : ℕ} (hs : s r = nst v) (ht : s t = []) (hd : s d = []) :
    (seq (moveAll r t) (dupAll t r d)).RunsLe s (update s d (nst v))
      (16 * (nst v).length + 2) := by
  have h2 := moveAll_runs hrt (nst v) s hs
  have h3 := dupAll_runs hrt.symm hdt.symm hrd (m := 0) ((nst v).reverse)
    (update (update s r []) t ((nst v).reverse ++ s t)) (by simp [ht])
  refine (h2.seq h3).of_eq ?_ (by simp; omega)
  funext k
  simp only [update_apply]
  split_ifs <;> simp_all

/-! ## Case distinctions on top bits -/

/-- Branch on the top bit of `i` (`true` iff the top is `1`). -/
def bit1 (i : Fin K) (f : Bool → Prog K 0) : Prog K 0 :=
  ite (fun t => t i == some 1) (f true) (f false)

lemma bit1_runs {i : Fin K} {f : Bool → Prog K 0} {s s' : Stacks K 0} {T : ℕ} {a : Bool}
    (ha : (tops s i == some 1) = a) (h : (f a).RunsLe s s' T) :
    (bit1 i f).RunsLe s s' (T + 1) := by
  cases a
  · exact h.iteF ha
  · exact h.iteT ha

/-- Branch on the top bits of `i` and `j`. -/
def bit2 (i j : Fin K) (f : Bool → Bool → Prog K 0) : Prog K 0 :=
  bit1 i fun a => bit1 j fun b => f a b

lemma bit2_runs {i j : Fin K} {f : Bool → Bool → Prog K 0} {s s' : Stacks K 0} {T : ℕ}
    {a b : Bool} (ha : (tops s i == some 1) = a) (hb : (tops s j == some 1) = b)
    (h : (f a b).RunsLe s s' T) : (bit2 i j f).RunsLe s s' (T + 2) :=
  bit1_runs ha (bit1_runs hb h)

/-- Branch on the top bits of `i`, `j` and `k`. -/
def bit3 (i j k : Fin K) (f : Bool → Bool → Bool → Prog K 0) : Prog K 0 :=
  bit1 i fun a => bit1 j fun b => bit1 k fun c => f a b c

lemma bit3_runs {i j k : Fin K} {f : Bool → Bool → Bool → Prog K 0} {s s' : Stacks K 0}
    {T : ℕ} {a b c : Bool} (ha : (tops s i == some 1) = a) (hb : (tops s j == some 1) = b)
    (hc : (tops s k == some 1) = c) (h : (f a b c).RunsLe s s' T) :
    (bit3 i j k f).RunsLe s s' (T + 3) :=
  bit1_runs ha (bit1_runs hb (bit1_runs hc h))

lemma tops_bs (s : Stacks K 0) (i : Fin K) (l : List Bool) (hs : s i = bs l) :
    (tops s i == some 1) = l.headD false := by
  cases l with
  | nil => simp [tops, hs]
  | cons b l => cases b <;> simp [tops, hs]

/-! ## Addition -/

/-- The carry as a stack. -/
def carrySt (c : Bool) : List Sym := if c then [1] else []

@[simp] lemma carrySt_true : carrySt true = [1] := rfl
@[simp] lemma carrySt_false : carrySt false = [] := rfl

/-- One step of the ripple-carry adder on `r` and `b` with carry stack `c`, writing the sum
digit onto `o`. -/
def addLeaf (r b c o : Fin K) (x y z : Bool) : Prog K 0 :=
  seq (pop r) (seq (pop b) (seq (pop c) (seq (push o (sym (Bool.xor (Bool.xor x y) z)))
    (if maj x y z then push c 1 else skip))))

/-- The ripple-carry loop. -/
def ripple (r b c o : Fin K) : Prog K 0 :=
  loop (fun t => (t r).isSome || (t b).isSome || (t c).isSome) (bit3 r b c (addLeaf r b c o))

section Ripple

variable {r b c o : Fin K} (hrb : r ≠ b) (hrc : r ≠ c) (hro : r ≠ o) (hbc : b ≠ c)
  (hbo : b ≠ o) (hco : c ≠ o)
include hrb hrc hro hbc hbo hco

lemma addLeaf_runs {s : Stacks K 0} {x y z : Bool} {l l' : List Bool}
    (hr : (s r).tail = bs l) (hb : (s b).tail = bs l') (hc : s c = carrySt z) :
    (addLeaf r b c o x y z).RunsLe s
      (update (update (update (update s r (bs l)) b (bs l')) c (carrySt (maj x y z))) o
        (sym (Bool.xor (Bool.xor x y) z) :: s o)) 7 := by
  have e3 : (s c).tail = [] := by rw [hc]; cases z <;> rfl
  unfold addLeaf
  cases hm : maj x y z
  · simp only [Bool.false_eq_true, if_false, carrySt_false]
    refine ((RunsLe.pop r s).seq ((RunsLe.pop b _).seq ((RunsLe.pop c _).seq
      ((RunsLe.push o _ _).seq (RunsLe.skip _))))).of_eq ?_ (by norm_num)
    funext k
    simp only [update_apply]
    split_ifs <;> simp_all
  · simp only [if_true, carrySt_true]
    refine ((RunsLe.pop r s).seq ((RunsLe.pop b _).seq ((RunsLe.pop c _).seq
      ((RunsLe.push o _ _).seq (RunsLe.push c 1 _))))).of_eq ?_ (by norm_num)
    funext k
    simp only [update_apply]
    split_ifs with h1 h2 h3 h4 h5 h6 h7 <;> subst_vars <;> simp_all

lemma ripple_nil (z : Bool) (s : Stacks K 0) (hr : s r = []) (hb : s b = [])
    (hc : s c = carrySt z) :
    (ripple r b c o).RunsLe s
      (update (update (update (update s r []) b []) c []) o ((bs (addL [] [] z)).reverse ++ s o))
      (11 * (addL [] [] z).length + 1) := by
  cases z
  · refine (RunsLe.loopF (by simp [tops, hr, hb, hc])).of_eq ?_ (by simp [addL])
    funext k
    simp only [update_apply, addL]
    split_ifs <;> simp_all
  · refine (RunsLe.loopT (by simp [tops, hc]) (bit3_runs (a := false) (b := false)
      (c := true) (by rw [tops_bs s r [] hr]; rfl) (by rw [tops_bs s b [] hb]; rfl)
      (by simp [tops, hc]) (addLeaf_runs hrb hrc hro hbc hbo hco (l := []) (l' := [])
        (by simp [hr]) (by simp [hb]) hc))
      (RunsLe.loopF ?_)).of_eq ?_ (by simp [addL])
    · simp [tops, update_of_ne hrb, update_of_ne hrc, update_of_ne hro, update_of_ne hbc,
        update_of_ne hbo, update_of_ne hco, maj]
    · funext k
      simp only [update_apply, addL]
      split_ifs <;> simp_all [maj]

lemma ripple_runs : ∀ (l l' : List Bool) (z : Bool) (s : Stacks K 0), s r = bs l →
    s b = bs l' → s c = carrySt z →
    (ripple r b c o).RunsLe s
      (update (update (update (update s r []) b []) c []) o ((bs (addL l l' z)).reverse ++ s o))
      (11 * (addL l l' z).length + 1)
  | [], [], z, s, hr, hb, hc => ripple_nil hrb hrc hro hbc hbo hco z s hr hb hc
  | x :: l, [], z, s, hr, hb, hc => by
    refine (RunsLe.loopT (by simp [tops, hr]) (bit3_runs (a := x) (b := false)
      (c := z) (by rw [tops_bs s r _ hr]; rfl) (by rw [tops_bs s b [] hb]; rfl)
      (by cases z <;> simp [tops, hc]) (addLeaf_runs hrb hrc hro hbc hbo hco (l := l) (l' := [])
        (by simp [hr]) (by simp [hb]) hc))
      (ripple_runs l [] (x && z) _ ?_ ?_ ?_)).of_eq ?_ (by simp [addL]; omega)
    · simp [update_of_ne hrb, update_of_ne hrc, update_of_ne hro]
    · simp [update_of_ne hbc, update_of_ne hbo]
    · simp [update_of_ne hco, maj]
    · funext k
      simp only [update_apply, addL]
      split_ifs <;> simp_all
  | [], y :: l', z, s, hr, hb, hc => by
    refine (RunsLe.loopT (by simp [tops, hb]) (bit3_runs (a := false) (b := y)
      (c := z) (by rw [tops_bs s r [] hr]; rfl) (by rw [tops_bs s b _ hb]; rfl)
      (by cases z <;> simp [tops, hc]) (addLeaf_runs hrb hrc hro hbc hbo hco (l := []) (l' := l')
        (by simp [hr]) (by simp [hb]) hc))
      (ripple_runs [] l' (y && z) _ ?_ ?_ ?_)).of_eq ?_ (by simp [addL]; omega)
    · simp [update_of_ne hrb, update_of_ne hrc, update_of_ne hro]
    · simp [update_of_ne hbc, update_of_ne hbo]
    · simp [update_of_ne hco, maj]
    · funext k
      simp only [update_apply, addL]
      split_ifs <;> simp_all
  | x :: l, y :: l', z, s, hr, hb, hc => by
    refine (RunsLe.loopT (by simp [tops, hr]) (bit3_runs (a := x) (b := y)
      (c := z) (by rw [tops_bs s r _ hr]; rfl) (by rw [tops_bs s b _ hb]; rfl)
      (by cases z <;> simp [tops, hc]) (addLeaf_runs hrb hrc hro hbc hbo hco (l := l) (l' := l')
        (by simp [hr]) (by simp [hb]) hc))
      (ripple_runs l l' (maj x y z) _ ?_ ?_ ?_)).of_eq ?_ (by simp [addL]; omega)
    · simp [update_of_ne hrb, update_of_ne hrc, update_of_ne hro]
    · simp [update_of_ne hbc, update_of_ne hbo]
    · simp [update_of_ne hco]
    · funext k
      simp only [update_apply, addL]
      split_ifs <;> simp_all
  termination_by l l' => l.length + l'.length

end Ripple

end Lax119563Proofs.Reduction

end Reduction_HStack

/-! ### Formerly `Lax119563Proofs.Reduction.HRoutines` -/

section Reduction_HRoutines

/-!
# Binary registers on stacks: addition, comparison, output, input

Stack routines for `add`, `lt`, `emit`, `rd` and `rst` of `HProg`.
-/

open Function Lax119563.BinaryEncodings

namespace Lax119563Proofs.Reduction

open Hierarchy Hierarchy.Prog
open Machines (valBits valBits_bits)

variable {K : ℕ}

/-- Copy `r` onto the empty stack `d` through the empty helper `t`. -/
def copyE (r d t : Fin K) : Prog K 0 := seq (moveAll r t) (dupAll t r d)

/-! ## Addition -/

/-- `r := r + b` with empty helpers `t₀, t₁, t₂`. -/
def hAdd (r b t₀ t₁ t₂ : Fin K) : Prog K 0 :=
  seq (copyE b t₁ t₀) (seq (ripple r t₁ t₂ t₀) (moveAll t₀ r))

lemma hAdd_runs {r b t₀ t₁ t₂ : Fin K} (hrb : r ≠ b) (hr0 : r ≠ t₀) (hr1 : r ≠ t₁)
    (hr2 : r ≠ t₂) (hb0 : b ≠ t₀) (hb1 : b ≠ t₁) (hb2 : b ≠ t₂) (h01 : t₀ ≠ t₁)
    (h02 : t₀ ≠ t₂) (h12 : t₁ ≠ t₂) {s : Stacks K 0} {u v : ℕ} (hr : s r = nst u)
    (hb : s b = nst v) (h0 : s t₀ = []) (h1 : s t₁ = []) (h2 : s t₂ = []) :
    (hAdd r b t₀ t₁ t₂).RunsLe s (update s r (nst (u + v)))
      (16 * (nst v).length + 17 * (nst (u + v)).length + 4) := by
  have c1 := hCopy_runs_empty hb1 hb0 h01.symm hb h0 h1
  have c2 := ripple_runs hr1 hr2 hr0 h12 h01.symm h02.symm (Nat.bits u) (Nat.bits v) false
    (update s t₁ (nst v)) (by simp [update_of_ne hr1, hr, nst]) (by simp [nst])
    (by simp [update_of_ne h12.symm, h2])
  have e : (bs (addL (Nat.bits u) (Nat.bits v) false)) = nst (u + v) := by
    rw [nst, bits_add]
  rw [e] at c2
  refine (c1.seq (c2.seq (moveAll_runs hr0.symm (m := 0) ((nst (u + v)).reverse) _ ?_))).of_eq
    ?_ ?_
  · simp [update_of_ne h01, h0]
  · funext k
    simp only [update_apply]
    split_ifs <;> simp_all
  · have : (addL (Nat.bits u) (Nat.bits v) false).length = (nst (u + v)).length := by
      rw [← e]; simp
    simp only [List.length_reverse, this]; omega

/-! ## Comparison -/

/-- A comparison result as a stack. -/
def ordSt : Ordering → List Sym
  | .lt => [1]
  | .gt => [0]
  | .eq => []

@[simp] lemma ordSt_tail (o : Ordering) : (ordSt o).tail = [] := by cases o <;> rfl

/-- One step of the comparison scan of `i` and `j`, with the result so far on `k`. -/
def cmpLeaf (i j k : Fin K) (x y : Bool) : Prog K 0 :=
  seq (pop i) (seq (pop j) (if x = y then skip else seq (pop k) (push k (if y then 1 else 0))))

/-- The comparison scan. -/
def cmpLoop (i j k : Fin K) : Prog K 0 :=
  loop (fun t => (t i).isSome || (t j).isSome) (bit2 i j (cmpLeaf i j k))

section Cmp

variable {i j k : Fin K} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
include hij hik hjk

lemma cmpLeaf_runs {s : Stacks K 0} {x y : Bool} {l l' : List Bool} {o : Ordering}
    (hi : (s i).tail = bs l) (hj : (s j).tail = bs l') (hk : s k = ordSt o) :
    (cmpLeaf i j k x y).RunsLe s
      (update (update (update s i (bs l)) j (bs l')) k (ordSt ((compare x y).then o))) 6 := by
  unfold cmpLeaf
  by_cases hxy : x = y
  · subst hxy
    simp only [if_true]
    refine ((RunsLe.pop i s).seq ((RunsLe.pop j _).seq (RunsLe.skip _))).of_eq ?_ (by norm_num)
    funext k'
    have e : (compare x x).then o = o := by cases x <;> rfl
    simp only [update_apply, e]
    split_ifs <;> simp_all
  · simp only [hxy, if_false]
    refine ((RunsLe.pop i s).seq ((RunsLe.pop j _).seq ((RunsLe.pop k _).seq
      (RunsLe.push k _ _)))).of_eq ?_ (by norm_num)
    have e : ordSt ((compare x y).then o) = [if y then 1 else 0] := by
      cases x <;> cases y <;> simp_all [ordSt, compare, compareOfLessAndEq]
    have e2 : (s k).tail = [] := by rw [hk]; cases o <;> rfl
    funext k'
    simp only [update_apply, e]
    split_ifs <;> simp_all

lemma cmpLoop_runs : ∀ (l l' : List Bool) (o : Ordering) (s : Stacks K 0), s i = bs l →
    s j = bs l' → s k = ordSt o →
    (cmpLoop i j k).RunsLe s (update (update (update s i []) j []) k (ordSt (cmpL l l' o)))
      (9 * (l.length + l'.length) + 1)
  | [], [], o, s, hi, hj, hk => by
    refine (RunsLe.loopF (by simp [tops, hi, hj])).of_eq ?_ (by simp)
    funext k'
    simp only [update_apply, cmpL]
    split_ifs <;> simp_all
  | x :: l, [], o, s, hi, hj, hk => by
    refine (RunsLe.loopT (by simp [tops, hi]) (bit2_runs (a := x) (b := false)
      (by rw [tops_bs s i _ hi]; rfl) (by rw [tops_bs s j [] hj]; rfl)
      (cmpLeaf_runs hij hik hjk (l := l) (l' := []) (by simp [hi]) (by simp [hj]) hk))
      (cmpLoop_runs l [] ((compare x false).then o) _ ?_ ?_ ?_)).of_eq ?_ (by simp; omega)
    · simp [update_of_ne hij, update_of_ne hik]
    · simp [update_of_ne hjk]
    · simp
    · funext k'
      simp only [update_apply, cmpL]
      split_ifs <;> simp_all
  | [], y :: l', o, s, hi, hj, hk => by
    refine (RunsLe.loopT (by simp [tops, hj]) (bit2_runs (a := false) (b := y)
      (by rw [tops_bs s i [] hi]; rfl) (by rw [tops_bs s j _ hj]; rfl)
      (cmpLeaf_runs hij hik hjk (l := []) (l' := l') (by simp [hi]) (by simp [hj]) hk))
      (cmpLoop_runs [] l' ((compare false y).then o) _ ?_ ?_ ?_)).of_eq ?_ (by simp; omega)
    · simp [update_of_ne hij, update_of_ne hik]
    · simp [update_of_ne hjk]
    · simp
    · funext k'
      simp only [update_apply, cmpL]
      split_ifs <;> simp_all
  | x :: l, y :: l', o, s, hi, hj, hk => by
    refine (RunsLe.loopT (by simp [tops, hi]) (bit2_runs (a := x) (b := y)
      (by rw [tops_bs s i _ hi]; rfl) (by rw [tops_bs s j _ hj]; rfl)
      (cmpLeaf_runs hij hik hjk (l := l) (l' := l') (by simp [hi]) (by simp [hj]) hk))
      (cmpLoop_runs l l' ((compare x y).then o) _ ?_ ?_ ?_)).of_eq ?_ (by simp; omega)
    · simp [update_of_ne hij, update_of_ne hik]
    · simp [update_of_ne hjk]
    · simp
    · funext k'
      simp only [update_apply, cmpL]
      split_ifs <;> simp_all
  termination_by l l' => l.length + l'.length

end Cmp

/-- `f := [a < b]` with empty helpers `t₀, …, t₃`. -/
def hLt (f a b t₀ t₁ t₂ t₃ : Fin K) : Prog K 0 :=
  seq (copyE a t₁ t₀) (seq (copyE b t₂ t₀) (seq (cmpLoop t₁ t₂ t₃) (seq (clear f)
    (seq (ite (fun t => t t₃ == some 1) (push f 1) skip) (pop t₃)))))

lemma nst_one : nst 1 = [1] := by
  have := nst_bit1 0; simpa using this

lemma hLt_runs {f a b t₀ t₁ t₂ t₃ : Fin K}
    (hfa : f ≠ a) (hfb : f ≠ b) (hf0 : f ≠ t₀) (hf1 : f ≠ t₁) (hf2 : f ≠ t₂) (hf3 : f ≠ t₃)
    (hab : a ≠ b) (ha0 : a ≠ t₀) (ha1 : a ≠ t₁) (ha2 : a ≠ t₂) (ha3 : a ≠ t₃)
    (hb0 : b ≠ t₀) (hb1 : b ≠ t₁) (hb2 : b ≠ t₂) (hb3 : b ≠ t₃)
    (h01 : t₀ ≠ t₁) (h02 : t₀ ≠ t₂) (h03 : t₀ ≠ t₃) (h12 : t₁ ≠ t₂) (h13 : t₁ ≠ t₃)
    (h23 : t₂ ≠ t₃) {s : Stacks K 0} {u v : ℕ} (ha : s a = nst u)
    (hb : s b = nst v) (h0 : s t₀ = []) (h1 : s t₁ = []) (h2 : s t₂ = []) (h3 : s t₃ = []) :
    (hLt f a b t₀ t₁ t₂ t₃).RunsLe s (update s f (nst (if u < v then 1 else 0)))
      (2 * (s f).length + 25 * ((nst u).length + (nst v).length) + 12) := by
  have c1 := hCopy_runs_empty ha1 ha0 h01.symm ha h0 h1
  have c2 := hCopy_runs_empty hb2 hb0 h02.symm (s := update s t₁ (nst u)) (v := v)
    (by simp [update_of_ne hb1, hb]) (by simp [update_of_ne h01, h0])
    (by simp [update_of_ne h12.symm, h2])
  have c3 := cmpLoop_runs h12 h13 h23 (Nat.bits u) (Nat.bits v) .eq
    (update (update s t₁ (nst u)) t₂ (nst v)) (by simp [update_of_ne h12, nst])
    (by simp [nst]) (by simp [update_of_ne h13.symm, update_of_ne h23.symm, h3, ordSt])
  rw [cmpL_spec, valBits_bits, valBits_bits, Ordering.then_eq] at c3
  set s₃ := update (update (update (update (update s t₁ (nst u)) t₂ (nst v)) t₁ []) t₂ [])
    t₃ (ordSt (compare u v)) with hs₃
  have c4 := clear_runs f (s₃ f) s₃ rfl
  have hf3' : update s₃ f [] t₃ = ordSt (compare u v) := by
    simp [hs₃, update_of_ne hf3.symm]
  have c5 : (ite (fun t => t t₃ == some 1) (push f 1) skip : Prog K 0).RunsLe (update s₃ f [])
      (update (update s₃ f []) f (nst (if u < v then 1 else 0))) 3 := by
    rcases lt_trichotomy u v with huv | rfl | huv
    · refine ((RunsLe.push f 1 _).iteT ?_).of_eq ?_ le_rfl
      · simp [tops, hf3', compare_lt_iff_lt.mpr huv, ordSt]
      · simp [huv, nst_one]
    · refine ((RunsLe.skip _).iteF ?_).of_eq ?_ (by norm_num)
      · simp [tops, hf3', ordSt]
      · simp
    · refine ((RunsLe.skip _).iteF ?_).of_eq ?_ (by norm_num)
      · simp [tops, hf3', compare_gt_iff_gt.mpr huv, ordSt]
      · simp [not_lt.mpr huv.le]
  have c6 := RunsLe.pop t₃ (update (update s₃ f []) f (nst (if u < v then 1 else 0)))
  have hlen : ∀ o : Ordering, (ordSt o).length ≤ 1 := fun o => by cases o <;> simp [ordSt]
  refine (c1.seq (c2.seq (c3.seq (c4.seq (c5.seq c6))))).of_eq ?_ ?_
  · funext k
    simp only [hs₃, update_apply]
    split_ifs <;> simp_all
  · have : (s₃ f) = s f := by
      simp [hs₃, update_of_ne hf1, update_of_ne hf2, update_of_ne hf3]
    rw [this]; simp only [nst, length_bs]; omega

/-! ## Output -/

/-- Push the codes `1 d` of the digits on `i` onto `o`. -/
def emitLoop (i o : Fin K) : Prog K 0 :=
  loop (fun t => (t i).isSome) (bit1 i fun d => seq (pop i) (seq (push o 1) (push o (sym d))))

lemma emitLoop_runs {i o : Fin K} (hio : i ≠ o) : ∀ (l : List Bool) (s : Stacks K 0),
    s i = bs l →
    (emitLoop i o).RunsLe s
      (update (update s i []) o ((bs (l.flatMap fun d => [true, d])).reverse ++ s o))
      (7 * l.length + 1)
  | [], s, hs => by
    refine (RunsLe.loopF (by simp [tops, hs])).of_eq ?_ (by simp)
    funext k; simp only [update_apply]; split_ifs <;> simp_all
  | d :: l, s, hs => by
    refine (RunsLe.loopT (by simp [tops, hs]) (bit1_runs (a := d)
      (by rw [tops_bs s i _ hs]; rfl) ((RunsLe.pop i s).seq ((RunsLe.push o 1 _).seq
        (RunsLe.push o (sym d) _)))) (emitLoop_runs hio l _ ?_)).of_eq ?_ (by simp; omega)
    · simp [update_of_ne hio, hs]
    · funext k
      simp only [update_apply]
      split_ifs <;> simp_all [bs_append]

/-- Append `encodeNat` of `r` to the reversed output on `o`, with empty helpers `t₀, t₁`. -/
def hEmit (r o t₀ t₁ : Fin K) : Prog K 0 := seq (copyE r t₁ t₀) (seq (emitLoop t₁ o) (push o 0))

lemma bs_encodeNat_reverse (v : ℕ) :
    (bs (encodeNat v)).reverse = 0 :: (bs ((Nat.bits v).flatMap fun d => [true, d])).reverse := by
  simp [encodeNat, bs_append]

lemma hEmit_runs {r o t₀ t₁ : Fin K} (hro : r ≠ o) (hr0 : r ≠ t₀) (hr1 : r ≠ t₁)
    (ho0 : o ≠ t₀) (ho1 : o ≠ t₁) (h01 : t₀ ≠ t₁) {s : Stacks K 0} {v : ℕ}
    (hr : s r = nst v) (h0 : s t₀ = []) (h1 : s t₁ = []) :
    (hEmit r o t₀ t₁).RunsLe s (update s o ((bs (encodeNat v)).reverse ++ s o))
      (23 * (nst v).length + 5) := by
  have c1 := hCopy_runs_empty hr1 hr0 h01.symm hr h0 h1
  have c2 := emitLoop_runs ho1.symm (Nat.bits v) (update s t₁ (nst v)) (by simp [nst])
  have c3 := RunsLe.push o 0 (update (update (update s t₁ (nst v)) t₁ []) o
    ((bs ((Nat.bits v).flatMap fun d => [true, d])).reverse ++ update s t₁ (nst v) o))
  refine (c1.seq (c2.seq c3)).of_eq ?_ ?_
  · funext k
    simp only [update_apply, bs_encodeNat_reverse]
    split_ifs <;> simp_all
  · simp [nst]; omega

/-! ## Input -/

/-- Read the top bit of the remaining input `xr` into `r`. -/
def hRdA (r xr : Fin K) : Prog K 0 :=
  seq (clear r) (ite (fun t => t xr == some 1) (seq (push r 1) (push r 0))
    (ite (fun t => t xr == some 0) (push r 1) skip))

lemma hRdA_runs {r xr : Fin K} (hrr : r ≠ xr) {s : Stacks K 0} {l : List Bool}
    (hs : s xr = bs l) :
    (hRdA r xr).RunsLe s (update s r (nst (rdVal l))) (2 * (s r).length + 6) := by
  have c1 := clear_runs r (s r) s rfl
  have hxr : update s r [] xr = bs l := by simp [update_of_ne hrr.symm, hs]
  have c2 : (ite (fun t => t xr == some 1) (seq (push r 1) (push r 0))
      (ite (fun t => t xr == some 0) (push r 1) skip) : Prog K 0).RunsLe
      (update s r []) (update (update s r []) r (nst (rdVal l))) 5 := by
    cases l with
    | nil =>
      exact (((RunsLe.skip _).iteF (by simp [tops, hxr])).iteF (by simp [tops, hxr])).of_eq
        (by simp [rdVal]) (by norm_num)
    | cons d l =>
      cases d
      · exact (((RunsLe.push r 1 _).iteT (by simp [tops, hxr, bs, sym])).iteF
          (by simp [tops, hxr, bs, sym])).of_eq (by simp [rdVal, nst_one]) (by norm_num)
      · have e2 : nst 2 = [0, 1] := by
          have := nst_bit0 (v := 1) (by norm_num); rw [this, nst_one]
        exact (((RunsLe.push r 1 _).seq (RunsLe.push r 0 _)).iteT
          (by simp [tops, hxr, bs, sym])).of_eq (by simp [rdVal, e2]) (by norm_num)
  exact (c1.seq c2).of_eq (by simp) (by omega)

/-- Move the top symbol of the remaining input `xr` (if any) to `xl`. -/
def hRdB (xl xr : Fin K) : Prog K 0 := ite (fun t => (t xr).isSome) (moveOne xr xl) skip

/-- Read a bit of the remaining input. -/
def hRd (r xl xr : Fin K) : Prog K 0 := seq (hRdA r xr) (hRdB xl xr)

end Lax119563Proofs.Reduction

end Reduction_HRoutines

/-! ### Formerly `Lax119563Proofs.Reduction.StackOut` -/

section Reduction_StackOut

/-!
# Stack programs computing outputs

The big-step semantics `Prog.Runs` of stack programs (area `Hierarchy`) forgets the head
positions. For the output convention of `ComputesWithin` the output must start at cell `0`
of tape `0`, so we track the heads: `Prog.RunsH p (s, h) (s', h') t` additionally records the
head positions (a push moves the head left, a pop moves it right, also on an empty stack).

`Prog.computesWithin`: if `p` runs from the input stacks with head `0` and ends with `y` on
stack `0` and head `0` on tape `0`, then `p.toMachine ans` computes `y` from `x`.
-/

open Lax489179.TuringMachine Lax119563.DeterministicTime Lax119563Proofs.Hierarchy

namespace Lax119563Proofs.Reduction

variable {K m : ℕ}

namespace Prog

open Hierarchy.Prog

/-- Stack contents together with the head positions. -/
abbrev SH (K m : ℕ) := Stacks K m × (Fin K → ℤ)

/-- Big-step semantics with head positions. -/
inductive RunsH : Hierarchy.Prog K m → SH K m → SH K m → ℕ → Prop
  | skip {s} : RunsH .skip s s 1
  | push {i a s h} : RunsH (.push i a) (s, h)
      (Function.update s i (a :: s i), Function.update h i (h i - 1)) 2
  | pop {i s h} : RunsH (.pop i) (s, h)
      (Function.update s i (s i).tail, Function.update h i (h i + 1)) 1
  | seq {p q x₁ x₂ x₃ t₁ t₂} : RunsH p x₁ x₂ t₁ → RunsH q x₂ x₃ t₂ →
      RunsH (.seq p q) x₁ x₃ (t₁ + t₂)
  | iteT {c p q x x' t} : c (tops x.1) = true → RunsH p x x' t → RunsH (.ite c p q) x x' (t + 1)
  | iteF {c p q x x' t} : c (tops x.1) = false → RunsH q x x' t → RunsH (.ite c p q) x x' (t + 1)
  | loopF {c p x} : c (tops x.1) = false → RunsH (.loop c p) x x 1
  | loopT {c p x₁ x₂ x₃ t₁ t₂} : c (tops x₁.1) = true → RunsH p x₁ x₂ t₁ →
      RunsH (.loop c p) x₂ x₃ t₂ → RunsH (.loop c p) x₁ x₃ (t₁ + t₂ + 1)

/-- Every run can be equipped with head positions. -/
theorem Runs.runsH {p : Hierarchy.Prog K m} {s s' : Stacks K m} {t : ℕ} (h : p.Runs s s' t)
    (hd : Fin K → ℤ) : ∃ hd', RunsH p (s, hd) (s', hd') t := by
  induction h generalizing hd with
  | skip => exact ⟨hd, .skip⟩
  | push => exact ⟨_, .push⟩
  | pop => exact ⟨_, .pop⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨h₁, e₁⟩ := ih₁ hd
    obtain ⟨h₂, e₂⟩ := ih₂ h₁
    exact ⟨h₂, .seq e₁ e₂⟩
  | iteT hc _ ih => obtain ⟨h₁, e₁⟩ := ih hd; exact ⟨h₁, .iteT hc e₁⟩
  | iteF hc _ ih => obtain ⟨h₁, e₁⟩ := ih hd; exact ⟨h₁, .iteF hc e₁⟩
  | loopF hc => exact ⟨hd, .loopF hc⟩
  | loopT hc _ _ ih₁ ih₂ =>
    obtain ⟨h₁, e₁⟩ := ih₁ hd
    obtain ⟨h₂, e₂⟩ := ih₂ h₁
    exact ⟨h₂, .loopT hc e₁ e₂⟩

lemma head_noop (T : Tapes K (Fin (m + 3))) :
    (T.apply (noop T.read).1 (noop T.read).2).head = T.head := by
  funext j; simp [noop, Tapes.apply, Move.offset]

lemma head_pop (T : Tapes K (Fin (m + 3))) (i : Fin K) :
    (T.apply (popA i T.read).1 (popA i T.read).2).head =
      Function.update T.head i (T.head i + 1) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [popA, Tapes.apply, Move.offset]
  · simp [popA, Tapes.apply, Move.offset, hj]

lemma head_push (T : Tapes K (Fin (m + 3))) (i : Fin K) (a : Fin (m + 2)) :
    let T₁ := T.apply (pushL i T.read).1 (pushL i T.read).2
    (T₁.apply (pushW i a T₁.read).1 (pushW i a T₁.read).2).head =
      Function.update T.head i (T.head i - 1) := by
  intro T₁
  funext j
  by_cases hj : j = i
  · subst hj; simp [T₁, pushL, pushW, Tapes.apply, Move.offset]; ring
  · simp [T₁, pushL, pushW, Tapes.apply, Move.offset, hj]

/-- Correctness of the compiler, with head positions. -/
theorem compile_endsH {p : Hierarchy.Prog K m} {x x' : SH K m} {t : ℕ} (hp : RunsH p x x' t)
    {T : Tapes K (Fin (m + 3))} (hT : Rep x.1 T) (hh : T.head = x.2) :
    ∃ T', Rep x'.1 T' ∧ T'.head = x'.2 ∧ p.compile.Ends p.start T none T' t := by
  induction hp generalizing T with
  | skip => exact ⟨_, rep_noop hT, (head_noop T).trans hh, Mach.prim_ends _ _⟩
  | @push i a s h =>
    refine ⟨_, rep_push hT i a, ?_, Mach.seq_left_exit (Mach.prim_ends _ _) (Mach.prim_ends _ _)⟩
    rw [head_push]; subst hh; rfl
  | @pop i s h =>
    refine ⟨_, rep_pop hT i, ?_, Mach.prim_ends _ _⟩
    rw [head_pop]; subst hh; rfl
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨T₁, h₁, g₁, e₁⟩ := ih₁ hT hh
    obtain ⟨T₂, h₂, g₂, e₂⟩ := ih₂ h₁ g₁
    exact ⟨T₂, h₂, g₂, Mach.seq_left_exit e₁ e₂⟩
  | iteT hc _ ih =>
    obtain ⟨T', h', g', e⟩ := ih hT hh
    refine ⟨T', h', g', Mach.branch_true ?_ e⟩
    rw [hT.tops]; exact hc
  | iteF hc _ ih =>
    obtain ⟨T', h', g', e⟩ := ih hT hh
    refine ⟨T', h', g', Mach.branch_false ?_ e⟩
    rw [hT.tops]; exact hc
  | loopF hc =>
    refine ⟨T, hT, hh, Mach.loop_false ?_⟩
    rw [hT.tops]; exact hc
  | loopT hc _ _ ih₁ ih₂ =>
    obtain ⟨T₁, h₁, g₁, e₁⟩ := ih₁ hT hh
    obtain ⟨T₂, h₂, g₂, e₂⟩ := ih₂ h₁ g₁
    refine ⟨T₂, h₂, g₂, Mach.loop_true ?_ e₁ e₂⟩
    rw [hT.tops]; exact hc

end Prog

section Final

variable {Λ : Type} [Fintype Λ] [DecidableEq Λ] {n : ℕ}

/-- A halting run of a `Mach` ends in the configuration with the final tapes. -/
lemma Mach.toMachine_ends_tapes {M : Mach (n + 1) (Fin (m + 3)) Λ} {s q : Λ}
    {T T' : Tapes (n + 1) (Fin (m + 3))} {b : Bool} {t : ℕ}
    (h : M.Ends q T (some b) T' t) :
    (drun (M.toMachine s) t (M.cfg s q T)).answer = some b ∧
      (drun (M.toMachine s) t (M.cfg s q T)).tape = T'.tape := by
  generalize ho : (some b : Option Bool) = o at h
  induction h with
  | @halt q T b' hq =>
    cases ho
    rw [drun_succ]
    have : step (M.toMachine s) false (M.cfg s q T) = { M.cfg s q T with answer := some b } := by
      simp only [step, Mach.cfg, Mach.toMachine, Equiv.symm_apply_apply]
      rw [show (fun j => T.tape j (T.head j)) = T.read from rfl, hq]
    rw [this, drun_of_answer rfl]
    exact ⟨rfl, rfl⟩
  | exit hq => cases ho
  | @next q q' T w mv o T' t hq _ ih =>
    rw [drun_succ]
    have : step (M.toMachine s) false (M.cfg s q T) = M.cfg s q' (T.apply w mv) := by
      simp only [step, Mach.cfg, Mach.toMachine, Equiv.symm_apply_apply]
      rw [show (fun j => T.tape j (T.head j)) = T.read from rfl, hq]
      rfl
    rw [this]
    exact ih ho

end Final

/-- **Output of a stack program.** If `p` runs from the input stacks of `x` (heads at `0`) to
stacks with `y` on stack `0` and the head of tape `0` back at `0`, then the machine
`p.toMachine ans` computes `y` from `x` within `t + 1` steps. -/
theorem Prog.computesWithin {p : Hierarchy.Prog (K + 1) m}
    {ans : (Fin (K + 1) → Option (Fin (m + 2))) → Bool} {x y : List Bool}
    {s' : Stacks (K + 1) m} {hd' : Fin (K + 1) → ℤ} {t : ℕ}
    (h : Prog.RunsH p (inputStacks K m x, fun _ => 0) (s', hd') t)
    (hy : s' 0 = y.map (bitSym m)) (hh : hd' 0 = 0) :
    ComputesWithin (p.toMachine ans) x y (t + 1) := by
  obtain ⟨T', hT', hH', hE⟩ := Prog.compile_endsH h (rep_input K m x) rfl
  have hE' := Mach.seq_left_exit (M₂ := Mach.haltWith (fun r => ans (fun i => decSym (r i))))
    hE (Mach.haltWith_ends _ T')
  have := Mach.toMachine_ends_tapes (s := .inl p.start) hE'
  unfold ComputesWithin HaltsWithin
  rw [runOn_eq_drun, Hierarchy.Prog.toMachine, Mach.init_toMachine, this.1, this.2,
    Mach.init_toMachine]
  refine ⟨rfl, ?_⟩
  funext z
  show T'.tape 0 z = (inputTapes K m y).tape 0 z
  have h1 := hT' 0 z
  have h2 := rep_input K m y 0 z
  have h3 : (inputTapes K m y).head 0 = 0 := rfl
  rw [hH'] at h1
  rw [h1, h2, h3]
  simp [hh, hy, inputStacks]

end Lax119563Proofs.Reduction

end Reduction_StackOut

/-! ### Formerly `Lax119563Proofs.Reduction.HHeads` -/

section Reduction_HHeads

/-!
# Head positions of stack programs

`Prog.RunsLeH`: runs with head positions (`Prog.RunsH`) within a cost bound. A program that
never pushes or pops stack `i` (`Prog.Avoids i`) leaves the head of tape `i` in place, so its
stack-level runs (`RunsLe`) lift to runs with heads. Moving symbols off or onto a stack moves
its head by the number of symbols moved.
-/

open Function

namespace Lax119563Proofs.Reduction

open Hierarchy Hierarchy.Prog

variable {K m : ℕ}

namespace Prog

/-- `p` runs from `x` to `x'` (stacks with heads) within cost `T`. -/
def RunsLeH (p : Hierarchy.Prog K m) (x x' : SH K m) (T : ℕ) : Prop :=
  ∃ t ≤ T, RunsH p x x' t

lemma RunsLeH.mono {p : Hierarchy.Prog K m} {x x' : SH K m} {T T' : ℕ} (h : RunsLeH p x x' T)
    (hT : T ≤ T') : RunsLeH p x x' T' := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t, by omega, h⟩

lemma RunsLeH.seq {p q : Hierarchy.Prog K m} {x₁ x₂ x₃ : SH K m} {T₁ T₂ : ℕ}
    (h₁ : RunsLeH p x₁ x₂ T₁) (h₂ : RunsLeH q x₂ x₃ T₂) :
    RunsLeH (.seq p q) x₁ x₃ (T₁ + T₂) := by
  obtain ⟨t₁, ht₁, h₁⟩ := h₁; obtain ⟨t₂, ht₂, h₂⟩ := h₂
  exact ⟨t₁ + t₂, by omega, .seq h₁ h₂⟩

lemma RunsLeH.iteT {c} {p q : Hierarchy.Prog K m} {x x' : SH K m} {T : ℕ}
    (hc : c (tops x.1) = true) (h : RunsLeH p x x' T) : RunsLeH (.ite c p q) x x' (T + 1) := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t + 1, by omega, .iteT hc h⟩

lemma RunsLeH.iteF {c} {p q : Hierarchy.Prog K m} {x x' : SH K m} {T : ℕ}
    (hc : c (tops x.1) = false) (h : RunsLeH q x x' T) : RunsLeH (.ite c p q) x x' (T + 1) := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t + 1, by omega, .iteF hc h⟩

lemma RunsLeH.loopF {c} {p : Hierarchy.Prog K m} {x : SH K m} (hc : c (tops x.1) = false) :
    RunsLeH (.loop c p) x x 1 := ⟨1, le_rfl, .loopF hc⟩

lemma RunsLeH.loopT {c} {p : Hierarchy.Prog K m} {x₁ x₂ x₃ : SH K m} {T₁ T₂ : ℕ}
    (hc : c (tops x₁.1) = true) (h₁ : RunsLeH p x₁ x₂ T₁) (h₂ : RunsLeH (.loop c p) x₂ x₃ T₂) :
    RunsLeH (.loop c p) x₁ x₃ (T₁ + T₂ + 1) := by
  obtain ⟨t₁, ht₁, h₁⟩ := h₁; obtain ⟨t₂, ht₂, h₂⟩ := h₂
  exact ⟨t₁ + t₂ + 1, by omega, .loopT hc h₁ h₂⟩

lemma RunsLeH.of_eq {p : Hierarchy.Prog K m} {x x₁ x₂ : SH K m} {T T' : ℕ}
    (h : RunsLeH p x x₁ T) (hx : x₁ = x₂) (hT : T ≤ T') : RunsLeH p x x₂ T' :=
  hx ▸ h.mono hT

/-- `p` never pushes or pops stack `i`. -/
def Avoids (i : Fin K) : Hierarchy.Prog K m → Prop
  | .skip => True
  | .push j _ => j ≠ i
  | .pop j => j ≠ i
  | .seq p q => Avoids i p ∧ Avoids i q
  | .ite _ p q => Avoids i p ∧ Avoids i q
  | .loop _ p => Avoids i p

lemma RunsH.head_of_avoids {i : Fin K} {p : Hierarchy.Prog K m} {x x' : SH K m} {t : ℕ}
    (h : RunsH p x x' t) (ha : Avoids i p) : x'.2 i = x.2 i := by
  induction h with
  | skip => rfl
  | push => simp [update_of_ne (show i ≠ _ from fun e => ha e.symm)]
  | pop => simp [update_of_ne (show i ≠ _ from fun e => ha e.symm)]
  | seq _ _ ih₁ ih₂ => exact (ih₂ ha.2).trans (ih₁ ha.1)
  | iteT _ _ ih => exact ih ha.1
  | iteF _ _ ih => exact ih ha.2
  | loopF => rfl
  | loopT _ _ _ ih₁ ih₂ => exact (ih₂ ha).trans (ih₁ ha)

/-- A run of a program avoiding `i` lifts to a run with heads keeping the head of `i`. -/
lemma RunsLe.toH {i : Fin K} {p : Hierarchy.Prog K m} {s s' : Stacks K m} {T : ℕ}
    (h : p.RunsLe s s' T) (ha : Avoids i p) (hd : Fin K → ℤ) :
    ∃ hd', hd' i = hd i ∧ RunsLeH p (s, hd) (s', hd') T := by
  obtain ⟨t, ht, h⟩ := h
  obtain ⟨hd', h'⟩ := Runs.runsH h hd
  exact ⟨hd', h'.head_of_avoids ha, t, ht, h'⟩

/-! ## Moving symbols with heads -/

lemma pushTopOf_runsH (i j : Fin K) {s : Stacks K m} {hd : Fin K → ℤ} {a : Fin (m + 2)}
    (ha : tops s i = some a) :
    ∀ as : List (Fin (m + 2)), a ∈ as →
      RunsLeH (pushTopOf i j as) (s, hd) (update s j (a :: s j), update hd j (hd j - 1))
        (as.length + 2)
  | [], h => by simp at h
  | b :: as, h => by
    by_cases hb : b = a
    · subst hb
      exact (RunsLeH.iteT (by simp [ha]) ⟨2, le_rfl, RunsH.push⟩).mono (by simp)
    · have : a ∈ as := by simp at h; tauto
      exact ((pushTopOf_runsH i j ha as this).iteF (by simp [ha, Ne.symm hb])).mono (by simp)

lemma moveOne_runsH {i j : Fin K} (hij : i ≠ j) {s : Stacks K m} {hd : Fin K → ℤ}
    {a : Fin (m + 2)} {l : List (Fin (m + 2))} (hs : s i = a :: l) :
    RunsLeH (moveOne i j) (s, hd)
      (update (update s i l) j (a :: s j), update (update hd i (hd i + 1)) j (hd j - 1))
      (m + 5) := by
  have h1 := pushTopOf_runsH i j (s := s) (hd := hd) (by simp [tops, hs])
    (List.finRange (m + 2)) (List.mem_finRange a)
  have h2 : RunsLeH (pop i) (update s j (a :: s j), update hd j (hd j - 1))
      (update (update s j (a :: s j)) i (update s j (a :: s j) i).tail,
        update (update hd j (hd j - 1)) i (update hd j (hd j - 1) i + 1)) 1 :=
    ⟨1, le_rfl, RunsH.pop⟩
  refine (h1.seq h2).of_eq ?_ (by simp)
  refine Prod.ext ?_ ?_
  · funext k; simp only [update_apply]; split_ifs <;> simp_all
  · funext k; simp only [update_apply]; split_ifs <;> simp_all

lemma moveAll_runsH {i j : Fin K} (hij : i ≠ j) :
    ∀ (l : List (Fin (m + 2))) (s : Stacks K m) (hd : Fin K → ℤ), s i = l →
      RunsLeH (moveAll i j) (s, hd)
        (update (update s i []) j (l.reverse ++ s j),
          update (update hd i (hd i + l.length)) j (hd j - l.length))
        ((m + 6) * l.length + 1)
  | [], s, hd, hs => by
    refine (RunsLeH.loopF (p := moveOne i j) (c := fun r => (r i).isSome) (x := (s, hd))
      (by simp [tops, hs])).of_eq ?_ (by simp)
    refine Prod.ext ?_ ?_
    · funext k; simp only [update_apply]; split_ifs <;> simp_all
    · funext k; simp only [update_apply]; split_ifs <;> simp_all
  | a :: l, s, hd, hs => by
    have h1 := moveOne_runsH hij (hd := hd) hs
    have h2 := moveAll_runsH hij l (update (update s i l) j (a :: s j))
      (update (update hd i (hd i + 1)) j (hd j - 1)) (by simp [update_of_ne hij])
    refine (RunsLeH.loopT (c := fun r => (r i).isSome) (by simp [tops, hs]) h1 h2).of_eq ?_
      (le_of_eq (by simp only [List.length_cons]; ring))
    refine Prod.ext ?_ ?_
    · funext k; simp only [update_apply]; split_ifs <;> simp_all
    · funext k
      simp only [update_apply, List.length_cons]
      split_ifs <;> simp_all <;> push_cast <;> ring

end Prog

end Lax119563Proofs.Reduction

end Reduction_HHeads

/-! ### Formerly `Lax119563Proofs.Reduction.HCompile` -/

section Reduction_HCompile

/-!
# Compiling register programs to stack programs and machines

Stack layout for `R` registers (`R + 7` stacks over `Fin 2`):
* `0`: the unread input `x[pos..]` (the input tape; its head is at `pos`),
* `1`: the read input `x[..pos]`, reversed,
* `2`: the output `encodeNats out`, reversed,
* `3, …, 6`: empty helpers,
* `7 + r`: register `r` (binary digits, least significant on top).

`compileH_runs`: every run of `HProg` is simulated within the same cost.
`HProg.computesWithin`: the machine `p.machine` runs `p`, then moves the output to tape `0`;
if `p` ends with the cursor at `0` and emitted the numbers `out` with
`|x| ≤ |encodeNats out|`, then the machine computes `encodeNats out` from `x`.
-/

open Function Lax119563.BinaryEncodings Lax119563.DeterministicTime

namespace Lax119563Proofs.Reduction

open Hierarchy Hierarchy.Prog Prog

variable {R : ℕ}

/-! ## Layout -/

/-- The input stack. -/
def sIo : Fin (R + 7) := ⟨0, by omega⟩
/-- The read input. -/
def sXl : Fin (R + 7) := ⟨1, by omega⟩
/-- The output. -/
def sOut : Fin (R + 7) := ⟨2, by omega⟩
/-- Helpers. -/
def sT0 : Fin (R + 7) := ⟨3, by omega⟩
/-- Helpers. -/
def sT1 : Fin (R + 7) := ⟨4, by omega⟩
/-- Helpers. -/
def sT2 : Fin (R + 7) := ⟨5, by omega⟩
/-- Helpers. -/
def sT3 : Fin (R + 7) := ⟨6, by omega⟩
/-- Registers. -/
def sReg (r : Fin R) : Fin (R + 7) := ⟨r.val + 7, by omega⟩

/-- The stacks representing a state. -/
def enc (x : List Bool) (st : HSt R) : Stacks (R + 7) 0 := fun i =>
  if h : 7 ≤ i.val then nst (st.env ⟨i.val - 7, by omega⟩)
  else if i.val = 0 then bs (x.drop st.pos)
  else if i.val = 1 then (bs (x.take st.pos)).reverse
  else if i.val = 2 then (bs (encodeNats st.out)).reverse
  else []

section Layout

variable (x : List Bool) (st : HSt R)

@[simp] lemma enc_reg (r : Fin R) : enc x st (sReg r) = nst (st.env r) := by
  simp [enc, sReg]
@[simp] lemma enc_io : enc x st sIo = bs (x.drop st.pos) := by simp [enc, sIo]
@[simp] lemma enc_xl : enc x st sXl = (bs (x.take st.pos)).reverse := by simp [enc, sXl]
@[simp] lemma enc_out : enc x st sOut = (bs (encodeNats st.out)).reverse := by simp [enc, sOut]
@[simp] lemma enc_t0 : enc x st sT0 = [] := by simp [enc, sT0]
@[simp] lemma enc_t1 : enc x st sT1 = [] := by simp [enc, sT1]
@[simp] lemma enc_t2 : enc x st sT2 = [] := by simp [enc, sT2]
@[simp] lemma enc_t3 : enc x st sT3 = [] := by simp [enc, sT3]

end Layout

/-- Proves distinctness of layout indices. -/
macro "dist" : tactic =>
  `(tactic| (simp only [ne_eq, Fin.ext_iff, sIo, sXl, sOut, sT0, sT1, sT2, sT3, sReg] at *; omega))

lemma sReg_ne {r s : Fin R} (h : r ≠ s) : sReg r ≠ sReg s := by
  intro e; apply h; ext; simp [sReg, Fin.ext_iff] at e; omega

lemma enc_set (x : List Bool) (st : HSt R) (r : Fin R) (v : ℕ) :
    update (enc x st) (sReg r) (nst v) = enc x (st.set r v) := by
  funext i
  by_cases hi : i = sReg r
  · subst hi; simp
  · rw [update_of_ne hi]
    unfold enc
    split_ifs with h7
    · congr 1
      simp only [HSt.set_env]
      rw [update_of_ne]
      intro e; apply hi; ext; simp [sReg, ← e]; omega
    all_goals rfl

lemma enc_emit (x : List Bool) (st : HSt R) (v : ℕ) :
    update (enc x st) sOut ((bs (encodeNat v)).reverse ++ enc x st sOut) =
      enc x { st with out := st.out ++ [v] } := by
  funext i
  by_cases hi : i = sOut
  · subst hi
    simp [encodeNats, bs_append]
  · rw [update_of_ne hi]
    unfold enc
    have : i.val ≠ 2 := fun e => hi (Fin.ext e)
    simp [this]

lemma enc_advance (x : List Bool) (st : HSt R) (hp : st.pos ≤ x.length) :
    update (update (enc x st) sIo (bs (x.drop st.pos).tail)) sXl
        (bs ((x.drop st.pos).take 1) ++ enc x st sXl) =
      enc x { st with pos := min (st.pos + 1) x.length } := by
  have h1 : (x.drop st.pos).tail = x.drop (min (st.pos + 1) x.length) := by
    rw [List.tail_drop]
    rcases Nat.lt_or_ge st.pos x.length with h | h
    · rw [min_eq_left (by omega)]
    · rw [min_eq_right (by omega), List.drop_eq_nil_of_le (by omega),
        List.drop_eq_nil_of_le (by omega)]
  have h2 : (bs (x.take (min (st.pos + 1) x.length))).reverse =
      bs ((x.drop st.pos).take 1) ++ (bs (x.take st.pos)).reverse := by
    rcases Nat.lt_or_ge st.pos x.length with h | h
    · rw [min_eq_left (by omega), List.take_add, bs_append, List.reverse_append]
      congr 1
      have : ((x.drop st.pos).take 1).length ≤ 1 := by simp
      rcases hl : (x.drop st.pos).take 1 with _ | ⟨a, _ | ⟨b, l⟩⟩
      · rfl
      · rfl
      · rw [hl] at this; simp at this
    · have e : st.pos = x.length := by omega
      rw [min_eq_right (by omega), e]
      simp
  have hxi : (sXl : Fin (R + 7)) ≠ sIo := by dist
  funext i
  by_cases ha : i = sXl
  · subst ha; rw [update_self]; simp [h2]
  · rw [update_of_ne ha]
    by_cases hb : i = sIo
    · subst hb; rw [update_self]; simp [h1]
    · rw [update_of_ne hb]
      have h0 : i.val ≠ 0 := fun e => hb (Fin.ext e)
      have h1' : i.val ≠ 1 := fun e => ha (Fin.ext e)
      unfold enc
      simp [h0, h1']

lemma enc_rst (x : List Bool) (st : HSt R) :
    update (update (enc x st) sXl []) sIo ((enc x st sXl).reverse ++ enc x st sIo) =
      enc x { st with pos := 0 } := by
  have hxi : (sXl : Fin (R + 7)) ≠ sIo := by dist
  funext i
  by_cases hb : i = sIo
  · subst hb; rw [update_self]; simp [← bs_append]
  · rw [update_of_ne hb]
    by_cases ha : i = sXl
    · subst ha; rw [update_self]; simp
    · rw [update_of_ne ha]
      have h0 : i.val ≠ 0 := fun e => hb (Fin.ext e)
      have h1' : i.val ≠ 1 := fun e => ha (Fin.ext e)
      unfold enc
      simp [h0, h1']

lemma inBit_eq (x : List Bool) (pos : ℕ) : inBit x pos = rdVal (x.drop pos) := rfl

/-! ## Compilation -/

/-- The stack program of a register program. -/
def compileH : HProg R → Hierarchy.Prog (R + 7) 0
  | .clr r => clear (sReg r)
  | .one r => hOne (sReg r)
  | .dbl r => hDbl (sReg r)
  | .half r => hHalf (sReg r)
  | .copy r s => hCopy (sReg r) (sReg s) sT0
  | .add r s => hAdd (sReg r) (sReg s) sT0 sT1 sT2
  | .lt f a b => hLt (sReg f) (sReg a) (sReg b) sT0 sT1 sT2 sT3
  | .emit r => hEmit (sReg r) sOut sT0 sT1
  | .rd r => hRd (sReg r) sXl sIo
  | .rst => moveAll sXl sIo
  | .seq p q => .seq (compileH p) (compileH q)
  | .ite c p q => .ite (fun t => c fun r => (t (sReg r)).map (· == 1)) (compileH p) (compileH q)
  | .loop c p => .loop (fun t => c fun r => (t (sReg r)).map (· == 1)) (compileH p)

lemma tops_enc (x : List Bool) (st : HSt R) :
    (fun r => (tops (enc x st) (sReg r)).map (· == 1)) = st.view := by
  funext r
  simp only [tops, enc_reg, HSt.view]
  exact head_nst _

/-! ### Avoiding the input stack -/

section Avoid

variable {K : ℕ}

lemma avoids_clear {i j : Fin K} (h : j ≠ i) : Avoids i (clear j : Hierarchy.Prog K 0) := h

lemma avoids_pushTopOf {i a b : Fin K} (h : b ≠ i) :
    ∀ as : List Sym, Avoids i (pushTopOf a b as : Hierarchy.Prog K 0)
  | [] => trivial
  | _ :: as => ⟨h, avoids_pushTopOf h as⟩

lemma avoids_moveOne {i a b : Fin K} (ha : a ≠ i) (hb : b ≠ i) :
    Avoids i (moveOne a b : Hierarchy.Prog K 0) := ⟨avoids_pushTopOf hb _, ha⟩

lemma avoids_moveAll {i a b : Fin K} (ha : a ≠ i) (hb : b ≠ i) :
    Avoids i (moveAll a b : Hierarchy.Prog K 0) := avoids_moveOne ha hb

lemma avoids_dupAll {i a b c : Fin K} (ha : a ≠ i) (hb : b ≠ i) (hc : c ≠ i) :
    Avoids i (dupAll a b c : Hierarchy.Prog K 0) :=
  ⟨avoids_pushTopOf hb _, avoids_pushTopOf hc _, ha⟩

lemma avoids_copyE {i a b c : Fin K} (ha : a ≠ i) (hb : b ≠ i) (hc : c ≠ i) :
    Avoids i (copyE a b c : Hierarchy.Prog K 0) :=
  ⟨avoids_moveAll ha hc, avoids_dupAll hc ha hb⟩

lemma avoids_bit1 {i j : Fin K} {f : Bool → Hierarchy.Prog K 0} (h : ∀ a, Avoids i (f a)) :
    Avoids i (bit1 j f) := ⟨h true, h false⟩

lemma avoids_bit2 {i j k : Fin K} {f : Bool → Bool → Hierarchy.Prog K 0}
    (h : ∀ a b, Avoids i (f a b)) : Avoids i (bit2 j k f) :=
  avoids_bit1 fun a => avoids_bit1 fun b => h a b

lemma avoids_bit3 {i j k l : Fin K} {f : Bool → Bool → Bool → Hierarchy.Prog K 0}
    (h : ∀ a b c, Avoids i (f a b c)) : Avoids i (bit3 j k l f) :=
  avoids_bit1 fun a => avoids_bit1 fun b => avoids_bit1 fun c => h a b c

end Avoid

/-- Primitive instructions not touching the input. -/
def HProg.isArith : HProg R → Bool
  | .clr _ | .one _ | .dbl _ | .half _ | .copy .. | .add .. | .lt .. | .emit _ => true
  | _ => false

lemma avoids_compile_prim (p : HProg R) (hp : p.isArith = true) :
    Avoids sIo (compileH p) := by
  have hr : ∀ r : Fin R, sReg r ≠ sIo := fun r => by dist
  have h0 : (sT0 : Fin (R + 7)) ≠ sIo := by dist
  have h1 : (sT1 : Fin (R + 7)) ≠ sIo := by dist
  have h2 : (sT2 : Fin (R + 7)) ≠ sIo := by dist
  have h3 : (sT3 : Fin (R + 7)) ≠ sIo := by dist
  have ho : (sOut : Fin (R + 7)) ≠ sIo := by dist
  cases p with
  | clr r => exact avoids_clear (hr r)
  | one r => exact hr r
  | dbl r => exact ⟨hr r, trivial⟩
  | half r => exact hr r
  | copy r s => exact ⟨avoids_clear (hr s), avoids_moveAll (hr r) h0, avoids_dupAll h0 (hr r) (hr s)⟩
  | add r s =>
    refine ⟨avoids_copyE (hr s) h1 h0, avoids_bit3 (j := sReg r) (k := sT1) (l := sT2)
      fun a b c => ?_, avoids_moveAll h0 (hr r)⟩
    refine ⟨hr r, h1, h2, h0, ?_⟩
    split_ifs
    · exact h2
    · trivial
  | lt f a b =>
    refine ⟨avoids_copyE (hr a) h1 h0, avoids_copyE (hr b) h2 h0,
      avoids_bit2 (j := sT1) (k := sT2) fun u v => ?_,
      avoids_clear (hr f), ⟨hr f, trivial⟩, h3⟩
    refine ⟨h1, h2, ?_⟩
    split_ifs <;> first | trivial | exact ⟨h3, h3⟩
  | emit r =>
    exact ⟨avoids_copyE (hr r) h1 h0, avoids_bit1 (j := sT1)
      (f := fun d => .seq (.pop sT1) (.seq (.push sOut 1) (.push sOut (sym d))))
      fun d => ⟨h1, ho, ho⟩, ho⟩
  | _ => simp [HProg.isArith] at hp

/-! ### Simulation -/

lemma unitCost_ge {w a : ℕ} (h : a ≤ 52 * w + 12) : a ≤ unitCost w := by
  unfold unitCost; omega

/-- **Simulation.** A run of `p` is a run of the compiled stack program within the same cost;
the head of the input tape follows the cursor. -/
theorem compileH_runs {x : List Bool} {w : ℕ} {p : HProg R} {st st' : HSt R} {t : ℕ}
    (h : HRuns x w p st st' t) (hpos : st.pos ≤ x.length) (hd : Fin (R + 7) → ℤ)
    (hhd : hd sIo = (st.pos : ℤ)) :
    ∃ hd' : Fin (R + 7) → ℤ, hd' sIo = (st'.pos : ℤ) ∧ RunsLeH (compileH p) (enc x st, hd) (enc x st', hd') t := by
  induction h generalizing hd with
  | @clr r st hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (clear_nst (sReg r) (enc_reg x st r))
      (avoids_compile_prim (.clr r) rfl) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq (by rw [enc_set]) ?_⟩
    have := length_nst_le hv
    exact unitCost_ge (by omega)
  | @one r st hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hOne_runs (sReg r) (enc_reg x st r))
      (avoids_compile_prim (.one r) rfl) hd
    exact ⟨hd', by simp [e, hhd], h'.of_eq (by rw [enc_set]) (unitCost_ge (by omega))⟩
  | @dbl r st hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hDbl_runs (sReg r) (enc_reg x st r))
      (avoids_compile_prim (.dbl r) rfl) hd
    exact ⟨hd', by simp [e, hhd], h'.of_eq (by rw [enc_set]) (unitCost_ge (by omega))⟩
  | @half r st hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hHalf_runs (sReg r) (enc_reg x st r))
      (avoids_compile_prim (.half r) rfl) hd
    exact ⟨hd', by simp [e, hhd], h'.of_eq (by rw [enc_set]) (unitCost_ge (by omega))⟩
  | @copy r s st hrs hr hs =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hCopy_runs (sReg_ne hrs) (by dist) (by dist)
      (enc_reg x st r) (enc_t0 x st)) (avoids_compile_prim (.copy r s) rfl) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq (by rw [enc_set]) ?_⟩
    have := length_nst_le hr
    have := length_nst_le hs
    simp only [enc_reg]
    exact unitCost_ge (by omega)
  | @add r s st hrs hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hAdd_runs (sReg_ne hrs) (by dist) (by dist) (by dist)
      (by dist) (by dist) (by dist) (by dist) (by dist) (by dist) (enc_reg x st r)
      (enc_reg x st s) (enc_t0 x st) (enc_t1 x st) (enc_t2 x st))
      (avoids_compile_prim (.add r s) rfl) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq (by rw [enc_set]) ?_⟩
    have := length_nst_le (show st.env s < 2 ^ w by omega)
    have := length_nst_le hv
    exact unitCost_ge (by omega)
  | @lt f a b st hfa hfb hab hf ha hb =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hLt_runs (sReg_ne hfa) (sReg_ne hfb) (by dist) (by dist)
      (by dist) (by dist) (sReg_ne hab) (by dist) (by dist) (by dist) (by dist) (by dist)
      (by dist) (by dist) (by dist) (by dist) (by dist) (by dist) (by dist) (by dist) (by dist)
      (enc_reg x st a) (enc_reg x st b) (enc_t0 x st) (enc_t1 x st) (enc_t2 x st)
      (enc_t3 x st)) (avoids_compile_prim (.lt f a b) rfl) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq (by rw [enc_set]) ?_⟩
    have := length_nst_le hf
    have := length_nst_le ha
    have := length_nst_le hb
    simp only [enc_reg]
    exact unitCost_ge (by omega)
  | @emit r st hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hEmit_runs (by dist) (by dist) (by dist) (by dist)
      (by dist) (by dist) (enc_reg x st r) (enc_t0 x st) (enc_t1 x st))
      (avoids_compile_prim (.emit r) rfl) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq (by rw [enc_emit]) ?_⟩
    have := length_nst_le hv
    exact unitCost_ge (by omega)
  | @rd r st hv hp =>
    have hA := hRdA_runs (r := sReg r) (xr := sIo) (by dist) (s := enc x st) (enc_io x st)
    rw [enc_set, ← inBit_eq] at hA
    obtain ⟨h₁, e₁, r₁⟩ := RunsLe.toH hA
      (show Avoids sIo (hRdA (sReg r) sIo : Hierarchy.Prog (R + 7) 0) from
        ⟨avoids_clear (by dist), ⟨(show sReg r ≠ sIo by dist), (show sReg r ≠ sIo by dist)⟩,
          (show sReg r ≠ sIo by dist), trivial⟩) hd
    have hio := enc_io x (st.set r (inBit x st.pos))
    simp only [HSt.set_pos] at hio
    have hlen := length_nst_le hv
    rcases hl : x.drop st.pos with _ | ⟨a, l⟩
    · have hpx : st.pos = x.length := by
        have := List.drop_eq_nil_iff.mp hl; omega
      have r₂ : RunsLeH (hRdB sXl sIo) (enc x (st.set r (inBit x st.pos)), h₁)
          (enc x (st.set r (inBit x st.pos)), h₁) 2 :=
        RunsLeH.iteF (by simp [tops, hio, hl]) ⟨1, le_rfl, .skip⟩
      refine ⟨h₁, by simp [e₁, hhd]; omega, (r₁.seq r₂).of_eq ?_ ?_⟩
      · congr 2
        ext <;> simp; omega
      · simp only [enc_reg]; exact unitCost_ge (by omega)
    · have r₂ := moveOne_runsH (show (sIo : Fin (R + 7)) ≠ sXl by dist) (m := 0)
        (s := enc x (st.set r (inBit x st.pos))) (hd := h₁) (a := sym a) (l := bs l)
        (by rw [hio, hl]; rfl)
      have r₂' := r₂.iteT (c := fun t => (t sIo).isSome) (q := skip) (by simp [tops, hio, hl])
      have hlt : st.pos < x.length := by
        by_contra hc; rw [List.drop_eq_nil_of_le (by omega)] at hl; cases hl
      refine ⟨update (update h₁ sIo (h₁ sIo + 1)) sXl (h₁ sXl - 1), ?_,
        (r₁.seq r₂').of_eq ?_ ?_⟩
      · rw [update_of_ne (show (sIo : Fin (R + 7)) ≠ sXl by dist), update_self, e₁, hhd]
        simp; omega
      · refine Prod.ext ?_ rfl
        have e := enc_advance x (st.set r (inBit x st.pos)) (by simpa using hp)
        simp only [HSt.set_pos, hl, List.tail_cons, List.take_succ_cons, List.take_zero,
          bs_cons, bs_nil, List.singleton_append] at e
        exact e
      · simp only [enc_reg]; exact unitCost_ge (by omega)
  | @rst st hp =>
    have h' := moveAll_runsH (show (sXl : Fin (R + 7)) ≠ sIo by dist) (m := 0)
      (enc x st sXl) (enc x st) hd rfl
    refine ⟨_, ?_, h'.of_eq (by rw [enc_rst]) ?_⟩
    · simp [hhd]; omega
    · simp only [enc_xl, List.length_reverse, length_bs, List.length_take, unitCost]
      have : min st.pos x.length = st.pos := by omega
      rw [this]; nlinarith
  | seq hr₁ _ ih₁ ih₂ =>
    obtain ⟨h₁, e₁, r₁⟩ := ih₁ hpos hd hhd
    obtain ⟨h₂, e₂, r₂⟩ := ih₂ (hr₁.pos_le hpos) h₁ e₁
    exact ⟨h₂, e₂, r₁.seq r₂⟩
  | iteT hc _ ih =>
    obtain ⟨h₁, e₁, r₁⟩ := ih hpos hd hhd
    exact ⟨h₁, e₁, r₁.iteT (by simp only [tops_enc]; exact hc)⟩
  | iteF hc _ ih =>
    obtain ⟨h₁, e₁, r₁⟩ := ih hpos hd hhd
    exact ⟨h₁, e₁, r₁.iteF (by simp only [tops_enc]; exact hc)⟩
  | loopF hc => exact ⟨hd, hhd, RunsLeH.loopF (by simp only [tops_enc]; exact hc)⟩
  | loopT hc hr₁ _ ih₁ ih₂ =>
    obtain ⟨h₁, e₁, r₁⟩ := ih₁ hpos hd hhd
    obtain ⟨h₂, e₂, r₂⟩ := ih₂ (hr₁.pos_le hpos) h₁ e₁
    exact ⟨h₂, e₂, RunsLeH.loopT (by simp only [tops_enc]; exact hc) r₁ r₂⟩

end Lax119563Proofs.Reduction

end Reduction_HCompile

/-! ### Formerly `Lax119563Proofs.Compiler.NProg` -/

section Compiler_NProg

/-!
# Register programs with number stacks

`NProg R Q` extends the register language `Reduction.HProg R` by `Q` *number stacks*, each
holding a list of naturals (top first):
* `spush q r`: push the value of register `r` onto stack `q`;
* `spop q r`: pop the top of the nonempty stack `q` into register `r`;
* conditions of `ite`/`loop` see the zero/parity view of the registers and whether each
  stack is nonempty (`NSt.view`).

Semantics `NRuns x w p st st' t` with the uniform word size `w` of `HRuns`: every primitive
requires the values it touches (registers, the pushed or popped number) to be `< 2^w` and
costs `unitCost w`. The compiler (`Compiler.NCompile`) simulates runs within the same cost;
stacks are stored as `bs (encodeNats vs)` (`Compiler.NumStack`).
-/

open Lax119563.BinaryEncodings Lax119563Proofs.Reduction

namespace Lax119563Proofs.Compiler

/-- The view used by conditions: registers (zero / parity) and stacks (nonempty). -/
abbrev NView (R Q : ℕ) := (Fin R → Option Bool) × (Fin Q → Bool)

/-- Programs over registers `Fin R` and number stacks `Fin Q`. -/
inductive NProg (R Q : ℕ) where
  | clr (r : Fin R)
  | one (r : Fin R)
  | dbl (r : Fin R)
  | half (r : Fin R)
  | copy (r s : Fin R)
  | add (r s : Fin R)
  | lt (f a b : Fin R)
  | emit (r : Fin R)
  | rd (r : Fin R)
  | rst
  | spush (q : Fin Q) (r : Fin R)
  | spop (q : Fin Q) (r : Fin R)
  | seq (p q : NProg R Q)
  | ite (c : NView R Q → Bool) (p q : NProg R Q)
  | loop (c : NView R Q → Bool) (p : NProg R Q)

/-- States: registers, number stacks, input cursor, emitted numbers. -/
@[ext]
structure NSt (R Q : ℕ) where
  env : Fin R → ℕ
  stk : Fin Q → List ℕ
  pos : ℕ
  out : List ℕ

namespace NSt

variable {R Q : ℕ}

/-- The view of a state. -/
def view (st : NSt R Q) : NView R Q :=
  (fun r => if st.env r = 0 then none else some (st.env r % 2 == 1),
    fun q => !(st.stk q).isEmpty)

/-- Set a register. -/
def set (st : NSt R Q) (r : Fin R) (v : ℕ) : NSt R Q :=
  { st with env := Function.update st.env r v }

/-- Replace a stack. -/
def setS (st : NSt R Q) (q : Fin Q) (l : List ℕ) : NSt R Q :=
  { st with stk := Function.update st.stk q l }

@[simp] lemma set_env (st : NSt R Q) (r : Fin R) (v : ℕ) :
    (st.set r v).env = Function.update st.env r v := rfl
@[simp] lemma set_stk (st : NSt R Q) (r : Fin R) (v : ℕ) : (st.set r v).stk = st.stk := rfl
@[simp] lemma set_pos (st : NSt R Q) (r : Fin R) (v : ℕ) : (st.set r v).pos = st.pos := rfl
@[simp] lemma set_out (st : NSt R Q) (r : Fin R) (v : ℕ) : (st.set r v).out = st.out := rfl
@[simp] lemma setS_env (st : NSt R Q) (q : Fin Q) (l : List ℕ) : (st.setS q l).env = st.env := rfl
@[simp] lemma setS_stk (st : NSt R Q) (q : Fin Q) (l : List ℕ) :
    (st.setS q l).stk = Function.update st.stk q l := rfl
@[simp] lemma setS_pos (st : NSt R Q) (q : Fin Q) (l : List ℕ) : (st.setS q l).pos = st.pos := rfl
@[simp] lemma setS_out (st : NSt R Q) (q : Fin Q) (l : List ℕ) : (st.setS q l).out = st.out := rfl

end NSt

variable {R Q : ℕ}

/-- Big-step semantics with word size `w` on input `x`. -/
inductive NRuns (x : List Bool) (w : ℕ) : NProg R Q → NSt R Q → NSt R Q → ℕ → Prop
  | clr {r st} : st.env r < 2 ^ w → NRuns x w (.clr r) st (st.set r 0) (unitCost w)
  | one {r st} : 2 * st.env r + 1 < 2 ^ w →
      NRuns x w (.one r) st (st.set r (2 * st.env r + 1)) (unitCost w)
  | dbl {r st} : 2 * st.env r < 2 ^ w → NRuns x w (.dbl r) st (st.set r (2 * st.env r)) (unitCost w)
  | half {r st} : st.env r < 2 ^ w → NRuns x w (.half r) st (st.set r (st.env r / 2)) (unitCost w)
  | copy {r s st} : r ≠ s → st.env r < 2 ^ w → st.env s < 2 ^ w →
      NRuns x w (.copy r s) st (st.set s (st.env r)) (unitCost w)
  | add {r s st} : r ≠ s → st.env r + st.env s < 2 ^ w →
      NRuns x w (.add r s) st (st.set r (st.env r + st.env s)) (unitCost w)
  | lt {f a b st} : f ≠ a → f ≠ b → a ≠ b → st.env f < 2 ^ w → st.env a < 2 ^ w →
      st.env b < 2 ^ w →
      NRuns x w (.lt f a b) st (st.set f (if st.env a < st.env b then 1 else 0)) (unitCost w)
  | emit {r st} : st.env r < 2 ^ w →
      NRuns x w (.emit r) st { st with out := st.out ++ [st.env r] } (unitCost w)
  | rd {r st} : st.env r < 2 ^ w → st.pos ≤ x.length →
      NRuns x w (.rd r) st
        { (st.set r (inBit x st.pos)) with pos := min (st.pos + 1) x.length } (unitCost w)
  | rst {st} : st.pos ≤ x.length →
      NRuns x w .rst st { st with pos := 0 } (unitCost w * (st.pos + 1))
  | spush {q r st} : st.env r < 2 ^ w →
      NRuns x w (.spush q r) st (st.setS q (st.env r :: st.stk q)) (unitCost w)
  | spop {q r st v vs} : st.env r < 2 ^ w → st.stk q = v :: vs → v < 2 ^ w →
      NRuns x w (.spop q r) st ((st.setS q vs).set r v) (unitCost w)
  | seq {p q st₁ st₂ st₃ t₁ t₂} : NRuns x w p st₁ st₂ t₁ → NRuns x w q st₂ st₃ t₂ →
      NRuns x w (.seq p q) st₁ st₃ (t₁ + t₂)
  | iteT {c p q st st' t} : c st.view = true → NRuns x w p st st' t →
      NRuns x w (.ite c p q) st st' (t + 1)
  | iteF {c p q st st' t} : c st.view = false → NRuns x w q st st' t →
      NRuns x w (.ite c p q) st st' (t + 1)
  | loopF {c p st} : c st.view = false → NRuns x w (.loop c p) st st 1
  | loopT {c p st₁ st₂ st₃ t₁ t₂} : c st₁.view = true → NRuns x w p st₁ st₂ t₁ →
      NRuns x w (.loop c p) st₂ st₃ t₂ → NRuns x w (.loop c p) st₁ st₃ (t₁ + t₂ + 1)

/-- The cursor stays within the input. -/
lemma NRuns.pos_le {x : List Bool} {w : ℕ} {p : NProg R Q} {st st' : NSt R Q} {t : ℕ}
    (h : NRuns x w p st st' t) (hp : st.pos ≤ x.length) : st'.pos ≤ x.length := by
  induction h with
  | rd => simp
  | rst => simp
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hp)
  | iteT _ _ ih => exact ih hp
  | iteF _ _ ih => exact ih hp
  | loopF => exact hp
  | loopT _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hp)
  | _ => simpa using hp

end Lax119563Proofs.Compiler

end Compiler_NProg

/-! ### Formerly `Lax119563Proofs.Compiler.NumStack` -/

section Compiler_NumStack

/-!
# Number stacks

A *number stack* holds a list of numbers `vs` (top number first) as the symbols
`bs (encodeNats vs)`: the same format as the input stack, so the top number reads like the
next number of an input. Routines on the stack machine (`Hierarchy.Prog K 0`):

* `nsPush r q t`: push the value `v` of the binary register `r` (`nst v`) onto `q`
  (`nsPush_runs`, cost `O(|bits v|)`, helper `t` empty before and after, `r` unchanged);
* `nsPop q r t`: pop the top number of `q` into `r` (`nsPop_runs`).
-/

open Function Lax119563.BinaryEncodings

namespace Lax119563Proofs.Compiler

open Hierarchy Hierarchy.Prog Lax119563Proofs.Reduction

variable {K : ℕ}

/-- The symbols of a pair code `1 d` per digit. -/
def pairs (l : List Bool) : List Bool := l.flatMap fun d => [true, d]

@[simp] lemma pairs_nil : pairs [] = [] := rfl
@[simp] lemma pairs_cons (d : Bool) (l : List Bool) : pairs (d :: l) = true :: d :: pairs l := rfl
lemma pairs_append (l l' : List Bool) : pairs (l ++ l') = pairs l ++ pairs l' := by
  simp [pairs]
@[simp] lemma length_pairs (l : List Bool) : (pairs l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons d l ih => simp [ih]; ring

lemma encodeNat_eq_pairs (v : ℕ) : encodeNat v = pairs (Nat.bits v) ++ [false] := rfl

/-! ## Push -/

/-- Pop the bits of `t` (most significant on top), pushing each back onto `r` and its code
`1 d` onto `q`. -/
def pushLoop (t r q : Fin K) : Prog K 0 :=
  loop (fun u => (u t).isSome)
    (bit1 t fun d => seq (pop t) (seq (push r (sym d)) (seq (push q (sym d)) (push q 1))))

lemma pushLoop_runs {t r q : Fin K} (htr : t ≠ r) (htq : t ≠ q) (hrq : r ≠ q) :
    ∀ (l : List Bool) (s : Stacks K 0), s t = bs l →
      (pushLoop t r q).RunsLe s
        (update (update (update s t []) r ((bs l).reverse ++ s r))
          q (bs (pairs l.reverse) ++ s q))
        (10 * l.length + 1)
  | [], s, hs => by
    refine (RunsLe.loopF (by simp [tops, hs])).of_eq ?_ (by simp)
    funext k; simp only [update_apply]; split_ifs <;> simp_all
  | d :: l, s, hs => by
    refine (RunsLe.loopT (by simp [tops, hs]) (bit1_runs (a := d)
      (by rw [tops_bs s t _ hs]; rfl) ((RunsLe.pop t s).seq ((RunsLe.push r (sym d) _).seq
        ((RunsLe.push q (sym d) _).seq (RunsLe.push q 1 _)))))
      (pushLoop_runs htr htq hrq l _ ?_)).of_eq ?_ (by simp; omega)
    · simp [update_of_ne htr, update_of_ne htq, hs]
    · funext k
      simp only [update_apply]
      split_ifs <;> simp_all [pairs_append, bs_append]

/-- Push the value of the register `r` onto the number stack `q` (helper `t`). -/
def nsPush (r q t : Fin K) : Prog K 0 :=
  seq (moveAll r t) (seq (push q 0) (pushLoop t r q))

lemma nsPush_runs {r q t : Fin K} (hrq : r ≠ q) (hrt : r ≠ t) (hqt : q ≠ t) {s : Stacks K 0}
    {v : ℕ} (hr : s r = nst v) (ht : s t = []) :
    (nsPush r q t).RunsLe s (update s q (bs (encodeNat v) ++ s q))
      (16 * (Nat.bits v).length + 5) := by
  have c1 := moveAll_runs hrt (m := 0) (nst v) s hr
  have c2 := RunsLe.push q 0 (update (update s r []) t ((nst v).reverse ++ s t))
  have c3 := pushLoop_runs hrt.symm hqt.symm hrq (Nat.bits v).reverse
    (update (update (update s r []) t ((nst v).reverse ++ s t)) q
      (0 :: update (update s r []) t ((nst v).reverse ++ s t) q))
    (by simp [update_of_ne hqt.symm, ht, nst, bs_reverse])
  refine (c1.seq (c2.seq c3)).of_eq ?_ ?_
  · funext k
    simp only [update_apply]
    split_ifs <;> simp_all [nst, bs_reverse, encodeNat_eq_pairs, bs_append]
  · simp [nst]; omega

/-! ## Pop -/

/-- Read the pair codes `1 d` on top of `q`, pushing the digits onto `t`. -/
def popLoop (q t : Fin K) : Prog K 0 :=
  loop (fun u => u q == some 1) (seq (pop q) (bit1 q fun d => seq (pop q) (push t (sym d))))

lemma popLoop_runs {q t : Fin K} (hqt : q ≠ t) (L : List Sym) :
    ∀ (l : List Bool) (s : Stacks K 0), s q = bs (pairs l) ++ 0 :: L →
      (popLoop q t).RunsLe s (update (update s q (0 :: L)) t ((bs l).reverse ++ s t))
        (7 * l.length + 1)
  | [], s, hs => by
    refine (RunsLe.loopF (by simp [tops, hs])).of_eq ?_ (by simp)
    funext k; simp only [update_apply]; split_ifs <;> simp_all
  | d :: l, s, hs => by
    have hs1 : update s q (s q).tail q = bs (d :: pairs l) ++ 0 :: L := by
      simp [hs]
    refine (RunsLe.loopT (by simp [tops, hs]) ((RunsLe.pop q s).seq (bit1_runs (a := d)
      (by cases d <;> simp [tops, hs, bs])
      ((RunsLe.pop q _).seq (RunsLe.push t (sym d) _))))
      (popLoop_runs hqt L l _ ?_)).of_eq ?_ (by simp; omega)
    · simp [update_of_ne hqt, hs]
    · funext k
      simp only [update_apply]
      split_ifs <;> simp_all

/-- Pop the top number of `q` into the register `r` (helper `t`). -/
def nsPop (q r t : Fin K) : Prog K 0 :=
  seq (clear r) (seq (popLoop q t) (seq (pop q) (moveAll t r)))

lemma nsPop_runs {q r t : Fin K} (hqr : q ≠ r) (hqt : q ≠ t) (hrt : r ≠ t) {s : Stacks K 0}
    {v : ℕ} {L : List Sym} (hq : s q = bs (encodeNat v) ++ L) (ht : s t = []) :
    (nsPop q r t).RunsLe s (update (update s q L) r (nst v))
      (2 * (s r).length + 13 * (Nat.bits v).length + 5) := by
  have c1 := clear_runs r (s r) s rfl
  have c2 := popLoop_runs hqt L (Nat.bits v) (update s r [])
    (by simp [update_of_ne hqr, hq, encodeNat_eq_pairs, bs_append])
  have c3 := RunsLe.pop q (update (update (update s r []) q (0 :: L)) t
    ((bs (Nat.bits v)).reverse ++ update s r [] t))
  have c4 := moveAll_runs (m := 0) hrt.symm (bs (Nat.bits v)).reverse
    (update (update (update (update s r []) q (0 :: L)) t
      ((bs (Nat.bits v)).reverse ++ update s r [] t)) q
      ((update (update (update s r []) q (0 :: L)) t
        ((bs (Nat.bits v)).reverse ++ update s r [] t)) q).tail)
    (by simp [update_of_ne hqt.symm, update_of_ne hrt.symm, ht])
  refine (c1.seq (c2.seq (c3.seq c4))).of_eq ?_ ?_
  · funext k
    simp only [update_apply]
    split_ifs <;> simp_all [nst]
  · simp; omega

end Lax119563Proofs.Compiler

end Compiler_NumStack

/-! ### Formerly `Lax119563Proofs.Compiler.NCompile` -/

section Compiler_NCompile

/-!
# Compiling register programs with number stacks to stack programs

Copy-generalised from `Reduction.HCompile` (which is left unchanged). Stack layout for `R`
registers and `Q` number stacks (`R + Q + 7` stacks over `Fin 2`):
* `0`: the unread input `x[pos..]`, `1`: the read input reversed, `2`: the output reversed,
* `3, …, 6`: empty helpers, `7 + r`: register `r` (`nst`),
* `7 + R + q`: number stack `q`, holding `bs (encodeNats (st.stk q))`.

`compileN_runs`: every run of `NProg` is simulated within the same cost.
-/

open Function Lax119563.BinaryEncodings Lax119563.DeterministicTime

namespace Lax119563Proofs.Compiler

open Hierarchy Hierarchy.Prog Lax119563Proofs.Reduction Lax119563Proofs.Reduction.Prog

variable {R Q : ℕ}

/-! ## Layout -/

/-- The unread input. -/
def nIo : Fin (R + Q + 7) := ⟨0, by omega⟩
/-- The read input. -/
def nXl : Fin (R + Q + 7) := ⟨1, by omega⟩
/-- The output. -/
def nOut : Fin (R + Q + 7) := ⟨2, by omega⟩
/-- Helpers. -/
def nT0 : Fin (R + Q + 7) := ⟨3, by omega⟩
/-- Helpers. -/
def nT1 : Fin (R + Q + 7) := ⟨4, by omega⟩
/-- Helpers. -/
def nT2 : Fin (R + Q + 7) := ⟨5, by omega⟩
/-- Helpers. -/
def nT3 : Fin (R + Q + 7) := ⟨6, by omega⟩
/-- Registers. -/
def nReg (r : Fin R) : Fin (R + Q + 7) := ⟨r.val + 7, by omega⟩
/-- Number stacks. -/
def nStk (q : Fin Q) : Fin (R + Q + 7) := ⟨q.val + 7 + R, by omega⟩

/-- The stacks representing a state. -/
def encN (x : List Bool) (st : NSt R Q) : Stacks (R + Q + 7) 0 := fun i =>
  if h : 7 + R ≤ i.val then bs (encodeNats (st.stk ⟨i.val - 7 - R, by omega⟩))
  else if h' : 7 ≤ i.val then nst (st.env ⟨i.val - 7, by omega⟩)
  else if i.val = 0 then bs (x.drop st.pos)
  else if i.val = 1 then (bs (x.take st.pos)).reverse
  else if i.val = 2 then (bs (encodeNats st.out)).reverse
  else []

/-- Closes goals about the layout of `encN`. -/
macro "layout_tac" : tactic =>
  `(tactic| (unfold encN; split_ifs <;>
    first | rfl | omega | (congr 2; ext; (try simp only [Fin.val_mk]); omega) |
      (congr 3; ext; (try simp only [Fin.val_mk]); omega)))

section Layout

variable (x : List Bool) (st : NSt R Q)

@[simp] lemma encN_reg (r : Fin R) : encN x st (nReg r) = nst (st.env r) := by
  have e : ((nReg r : Fin (R + Q + 7)) : ℕ) = r.val + 7 := rfl
  have := r.isLt
  layout_tac
@[simp] lemma encN_stk (q : Fin Q) : encN x st (nStk q) = bs (encodeNats (st.stk q)) := by
  have e : ((nStk q : Fin (R + Q + 7)) : ℕ) = q.val + 7 + R := rfl
  layout_tac
@[simp] lemma encN_io : encN x st nIo = bs (x.drop st.pos) := by
  have e : ((nIo : Fin (R + Q + 7)) : ℕ) = 0 := rfl
  layout_tac
@[simp] lemma encN_xl : encN x st nXl = (bs (x.take st.pos)).reverse := by
  have e : ((nXl : Fin (R + Q + 7)) : ℕ) = 1 := rfl
  layout_tac
@[simp] lemma encN_out : encN x st nOut = (bs (encodeNats st.out)).reverse := by
  have e : ((nOut : Fin (R + Q + 7)) : ℕ) = 2 := rfl
  layout_tac
@[simp] lemma encN_t0 : encN x st nT0 = [] := by
  have e : ((nT0 : Fin (R + Q + 7)) : ℕ) = 3 := rfl
  layout_tac
@[simp] lemma encN_t1 : encN x st nT1 = [] := by
  have e : ((nT1 : Fin (R + Q + 7)) : ℕ) = 4 := rfl
  layout_tac
@[simp] lemma encN_t2 : encN x st nT2 = [] := by
  have e : ((nT2 : Fin (R + Q + 7)) : ℕ) = 5 := rfl
  layout_tac
@[simp] lemma encN_t3 : encN x st nT3 = [] := by
  have e : ((nT3 : Fin (R + Q + 7)) : ℕ) = 6 := rfl
  layout_tac

end Layout

/-- Proves distinctness of layout indices. -/
macro "ndist" : tactic =>
  `(tactic| (simp only [ne_eq, Fin.ext_iff, nIo, nXl, nOut, nT0, nT1, nT2, nT3, nReg, nStk] at *; omega))

lemma nReg_ne {r s : Fin R} (h : r ≠ s) : (nReg r : Fin (R + Q + 7)) ≠ nReg s := by
  intro e; apply h; ext; simp [nReg, Fin.ext_iff] at e; omega

lemma encN_set (x : List Bool) (st : NSt R Q) (r : Fin R) (v : ℕ) :
    update (encN x st) (nReg r) (nst v) = encN x (st.set r v) := by
  funext i
  by_cases hi : i = nReg r
  · subst hi; simp
  · rw [update_of_ne hi]
    unfold encN
    split_ifs with h7R h7
    · rfl
    · congr 1
      simp only [NSt.set_env]
      rw [update_of_ne]
      intro e; apply hi; ext; simp [nReg, ← e]; omega
    all_goals rfl

lemma encN_setS (x : List Bool) (st : NSt R Q) (q : Fin Q) (l : List ℕ) :
    update (encN x st) (nStk q) (bs (encodeNats l)) = encN x (st.setS q l) := by
  funext i
  by_cases hi : i = nStk q
  · subst hi; simp
  · rw [update_of_ne hi]
    unfold encN
    split_ifs with h7R h7
    · congr 2
      simp only [NSt.setS_stk]
      rw [update_of_ne]
      intro e; apply hi; ext; simp [nStk, ← e]; omega
    all_goals rfl

lemma encN_emit (x : List Bool) (st : NSt R Q) (v : ℕ) :
    update (encN x st) nOut ((bs (encodeNat v)).reverse ++ encN x st nOut) =
      encN x { st with out := st.out ++ [v] } := by
  funext i
  by_cases hi : i = nOut
  · subst hi
    simp [encodeNats, bs_append]
  · rw [update_of_ne hi]
    unfold encN
    have : i.val ≠ 2 := fun e => hi (Fin.ext e)
    simp [this]

lemma encN_advance (x : List Bool) (st : NSt R Q) (hp : st.pos ≤ x.length) :
    update (update (encN x st) nIo (bs (x.drop st.pos).tail)) nXl
        (bs ((x.drop st.pos).take 1) ++ encN x st nXl) =
      encN x { st with pos := min (st.pos + 1) x.length } := by
  have h1 : (x.drop st.pos).tail = x.drop (min (st.pos + 1) x.length) := by
    rw [List.tail_drop]
    rcases Nat.lt_or_ge st.pos x.length with h | h
    · rw [min_eq_left (by omega)]
    · rw [min_eq_right (by omega), List.drop_eq_nil_of_le (by omega),
        List.drop_eq_nil_of_le (by omega)]
  have h2 : (bs (x.take (min (st.pos + 1) x.length))).reverse =
      bs ((x.drop st.pos).take 1) ++ (bs (x.take st.pos)).reverse := by
    rcases Nat.lt_or_ge st.pos x.length with h | h
    · rw [min_eq_left (by omega), List.take_add, bs_append, List.reverse_append]
      congr 1
      have : ((x.drop st.pos).take 1).length ≤ 1 := by simp
      rcases hl : (x.drop st.pos).take 1 with _ | ⟨a, _ | ⟨b, l⟩⟩
      · rfl
      · rfl
      · rw [hl] at this; simp at this
    · have e : st.pos = x.length := by omega
      rw [min_eq_right (by omega), e]
      simp
  have hxi : (nXl : Fin (R + Q + 7)) ≠ nIo := by ndist
  funext i
  by_cases ha : i = nXl
  · subst ha; rw [update_self]; simp [h2]
  · rw [update_of_ne ha]
    by_cases hb : i = nIo
    · subst hb; rw [update_self]; simp [h1]
    · rw [update_of_ne hb]
      have h0 : i.val ≠ 0 := fun e => hb (Fin.ext e)
      have h1' : i.val ≠ 1 := fun e => ha (Fin.ext e)
      unfold encN
      simp [h0, h1']

lemma encN_rst (x : List Bool) (st : NSt R Q) :
    update (update (encN x st) nXl []) nIo ((encN x st nXl).reverse ++ encN x st nIo) =
      encN x { st with pos := 0 } := by
  have hxi : (nXl : Fin (R + Q + 7)) ≠ nIo := by ndist
  funext i
  by_cases hb : i = nIo
  · subst hb; rw [update_self]; simp [← bs_append]
  · rw [update_of_ne hb]
    by_cases ha : i = nXl
    · subst ha; rw [update_self]; simp
    · rw [update_of_ne ha]
      have h0 : i.val ≠ 0 := fun e => hb (Fin.ext e)
      have h1' : i.val ≠ 1 := fun e => ha (Fin.ext e)
      unfold encN
      simp [h0, h1']

lemma inBit_eqN (x : List Bool) (pos : ℕ) : inBit x pos = rdVal (x.drop pos) := rfl

/-! ## Compilation -/

/-- The stack program of a register program. -/
def compileN : NProg R Q → Hierarchy.Prog (R + Q + 7) 0
  | .clr r => clear (nReg r)
  | .one r => hOne (nReg r)
  | .dbl r => hDbl (nReg r)
  | .half r => hHalf (nReg r)
  | .copy r s => hCopy (nReg r) (nReg s) nT0
  | .add r s => hAdd (nReg r) (nReg s) nT0 nT1 nT2
  | .lt f a b => hLt (nReg f) (nReg a) (nReg b) nT0 nT1 nT2 nT3
  | .emit r => hEmit (nReg r) nOut nT0 nT1
  | .rd r => hRd (nReg r) nXl nIo
  | .rst => moveAll nXl nIo
  | .spush q r => nsPush (nReg r) (nStk q) nT0
  | .spop q r => nsPop (nStk q) (nReg r) nT0
  | .seq p q => .seq (compileN p) (compileN q)
  | .ite c p q => .ite (fun t => c (fun r => (t (nReg r)).map (· == 1),
      fun q => (t (nStk q)).isSome)) (compileN p) (compileN q)
  | .loop c p => .loop (fun t => c (fun r => (t (nReg r)).map (· == 1),
      fun q => (t (nStk q)).isSome)) (compileN p)

lemma encodeNats_cons (v : ℕ) (l : List ℕ) :
    encodeNats (v :: l) = encodeNat v ++ encodeNats l := by simp [encodeNats]

lemma topsN_enc (x : List Bool) (st : NSt R Q) :
    ((fun r => (tops (encN x st) (nReg r)).map (· == 1)),
      (fun q => (tops (encN x st) (nStk q)).isSome)) = st.view := by
  refine Prod.ext ?_ ?_
  · funext r
    simp only [tops, encN_reg, NSt.view]
    exact head_nst _
  · funext q
    simp only [tops, encN_stk, NSt.view]
    cases h : st.stk q with
    | nil => simp [encodeNats]
    | cons v l => simp [encodeNats_cons, encodeNat, bs_append]

/-! ### Avoiding the input stack -/

section Avoid

variable {K : ℕ}

lemma avoids_clearN {i j : Fin K} (h : j ≠ i) : Avoids i (clear j : Hierarchy.Prog K 0) := h

lemma avoids_pushTopOfN {i a b : Fin K} (h : b ≠ i) :
    ∀ as : List Sym, Avoids i (pushTopOf a b as : Hierarchy.Prog K 0)
  | [] => trivial
  | _ :: as => ⟨h, avoids_pushTopOfN h as⟩

lemma avoids_moveOneN {i a b : Fin K} (ha : a ≠ i) (hb : b ≠ i) :
    Avoids i (moveOne a b : Hierarchy.Prog K 0) := ⟨avoids_pushTopOfN hb _, ha⟩

lemma avoids_moveAllN {i a b : Fin K} (ha : a ≠ i) (hb : b ≠ i) :
    Avoids i (moveAll a b : Hierarchy.Prog K 0) := avoids_moveOneN ha hb

lemma avoids_dupAllN {i a b c : Fin K} (ha : a ≠ i) (hb : b ≠ i) (hc : c ≠ i) :
    Avoids i (dupAll a b c : Hierarchy.Prog K 0) :=
  ⟨avoids_pushTopOfN hb _, avoids_pushTopOfN hc _, ha⟩

lemma avoids_copyEN {i a b c : Fin K} (ha : a ≠ i) (hb : b ≠ i) (hc : c ≠ i) :
    Avoids i (copyE a b c : Hierarchy.Prog K 0) :=
  ⟨avoids_moveAllN ha hc, avoids_dupAllN hc ha hb⟩

lemma avoids_bit1N {i j : Fin K} {f : Bool → Hierarchy.Prog K 0} (h : ∀ a, Avoids i (f a)) :
    Avoids i (bit1 j f) := ⟨h true, h false⟩

lemma avoids_bit2N {i j k : Fin K} {f : Bool → Bool → Hierarchy.Prog K 0}
    (h : ∀ a b, Avoids i (f a b)) : Avoids i (bit2 j k f) :=
  avoids_bit1N fun a => avoids_bit1N fun b => h a b

lemma avoids_bit3N {i j k l : Fin K} {f : Bool → Bool → Bool → Hierarchy.Prog K 0}
    (h : ∀ a b c, Avoids i (f a b c)) : Avoids i (bit3 j k l f) :=
  avoids_bit1N fun a => avoids_bit1N fun b => avoids_bit1N fun c => h a b c

end Avoid

/-- Primitive instructions not touching the input. -/
def NProg.isArith : NProg R Q → Bool
  | .clr _ | .one _ | .dbl _ | .half _ | .copy .. | .add .. | .lt .. | .emit _ => true
  | _ => false

lemma avoids_compile_primN (p : NProg R Q) (hp : p.isArith = true) :
    Avoids nIo (compileN p) := by
  have hr : ∀ r : Fin R, (nReg r : Fin (R + Q + 7)) ≠ nIo := fun r => by ndist
  have h0 : (nT0 : Fin (R + Q + 7)) ≠ nIo := by ndist
  have h1 : (nT1 : Fin (R + Q + 7)) ≠ nIo := by ndist
  have h2 : (nT2 : Fin (R + Q + 7)) ≠ nIo := by ndist
  have h3 : (nT3 : Fin (R + Q + 7)) ≠ nIo := by ndist
  have ho : (nOut : Fin (R + Q + 7)) ≠ nIo := by ndist
  cases p with
  | clr r => exact avoids_clearN (hr r)
  | one r => exact hr r
  | dbl r => exact ⟨hr r, trivial⟩
  | half r => exact hr r
  | copy r s => exact ⟨avoids_clearN (hr s), avoids_moveAllN (hr r) h0, avoids_dupAllN h0 (hr r) (hr s)⟩
  | add r s =>
    refine ⟨avoids_copyEN (hr s) h1 h0, avoids_bit3N (j := nReg r) (k := nT1) (l := nT2)
      fun a b c => ?_, avoids_moveAllN h0 (hr r)⟩
    refine ⟨hr r, h1, h2, h0, ?_⟩
    split_ifs
    · exact h2
    · trivial
  | lt f a b =>
    refine ⟨avoids_copyEN (hr a) h1 h0, avoids_copyEN (hr b) h2 h0,
      avoids_bit2N (j := nT1) (k := nT2) fun u v => ?_,
      avoids_clearN (hr f), ⟨hr f, trivial⟩, h3⟩
    refine ⟨h1, h2, ?_⟩
    split_ifs <;> first | trivial | exact ⟨h3, h3⟩
  | emit r =>
    exact ⟨avoids_copyEN (hr r) h1 h0, avoids_bit1N (j := nT1)
      (f := fun d => .seq (.pop nT1) (.seq (.push nOut 1) (.push nOut (sym d))))
      fun d => ⟨h1, ho, ho⟩, ho⟩
  | _ => simp [NProg.isArith] at hp

/-! ### Simulation -/

lemma unitCost_geN {w a : ℕ} (h : a ≤ 52 * w + 12) : a ≤ unitCost w := by
  unfold unitCost; omega

/-- **Simulation.** A run of `p` is a run of the compiled stack program within the same cost;
the head of the input tape follows the cursor. -/
theorem compileN_runs {x : List Bool} {w : ℕ} {p : NProg R Q} {st st' : NSt R Q} {t : ℕ}
    (h : NRuns x w p st st' t) (hpos : st.pos ≤ x.length) (hd : Fin (R + Q + 7) → ℤ)
    (hhd : hd nIo = (st.pos : ℤ)) :
    ∃ hd' : Fin (R + Q + 7) → ℤ, hd' nIo = (st'.pos : ℤ) ∧ RunsLeH (compileN p) (encN x st, hd) (encN x st', hd') t := by
  induction h generalizing hd with
  | @clr r st hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (clear_nst (nReg r) (encN_reg x st r))
      (avoids_compile_primN (.clr r) rfl) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq (by rw [encN_set]) ?_⟩
    have := length_nst_le hv
    exact unitCost_geN (by omega)
  | @one r st hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hOne_runs (nReg r) (encN_reg x st r))
      (avoids_compile_primN (.one r) rfl) hd
    exact ⟨hd', by simp [e, hhd], h'.of_eq (by rw [encN_set]) (unitCost_geN (by omega))⟩
  | @dbl r st hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hDbl_runs (nReg r) (encN_reg x st r))
      (avoids_compile_primN (.dbl r) rfl) hd
    exact ⟨hd', by simp [e, hhd], h'.of_eq (by rw [encN_set]) (unitCost_geN (by omega))⟩
  | @half r st hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hHalf_runs (nReg r) (encN_reg x st r))
      (avoids_compile_primN (.half r) rfl) hd
    exact ⟨hd', by simp [e, hhd], h'.of_eq (by rw [encN_set]) (unitCost_geN (by omega))⟩
  | @copy r s st hrs hr hs =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hCopy_runs (nReg_ne hrs) (by ndist) (by ndist)
      (encN_reg x st r) (encN_t0 x st)) (avoids_compile_primN (.copy r s) rfl) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq (by rw [encN_set]) ?_⟩
    have := length_nst_le hr
    have := length_nst_le hs
    simp only [encN_reg]
    exact unitCost_geN (by omega)
  | @add r s st hrs hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hAdd_runs (nReg_ne hrs) (by ndist) (by ndist) (by ndist)
      (by ndist) (by ndist) (by ndist) (by ndist) (by ndist) (by ndist) (encN_reg x st r)
      (encN_reg x st s) (encN_t0 x st) (encN_t1 x st) (encN_t2 x st))
      (avoids_compile_primN (.add r s) rfl) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq (by rw [encN_set]) ?_⟩
    have := length_nst_le (show st.env s < 2 ^ w by omega)
    have := length_nst_le hv
    exact unitCost_geN (by omega)
  | @lt f a b st hfa hfb hab hf ha hb =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hLt_runs (nReg_ne hfa) (nReg_ne hfb) (by ndist) (by ndist)
      (by ndist) (by ndist) (nReg_ne hab) (by ndist) (by ndist) (by ndist) (by ndist) (by ndist)
      (by ndist) (by ndist) (by ndist) (by ndist) (by ndist) (by ndist) (by ndist) (by ndist) (by ndist)
      (encN_reg x st a) (encN_reg x st b) (encN_t0 x st) (encN_t1 x st) (encN_t2 x st)
      (encN_t3 x st)) (avoids_compile_primN (.lt f a b) rfl) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq (by rw [encN_set]) ?_⟩
    have := length_nst_le hf
    have := length_nst_le ha
    have := length_nst_le hb
    simp only [encN_reg]
    exact unitCost_geN (by omega)
  | @emit r st hv =>
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (hEmit_runs (by ndist) (by ndist) (by ndist) (by ndist)
      (by ndist) (by ndist) (encN_reg x st r) (encN_t0 x st) (encN_t1 x st))
      (avoids_compile_primN (.emit r) rfl) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq (by rw [encN_emit]) ?_⟩
    have := length_nst_le hv
    exact unitCost_geN (by omega)
  | @rd r st hv hp =>
    have hA := hRdA_runs (r := nReg r) (xr := nIo) (by ndist) (s := encN x st) (encN_io x st)
    rw [encN_set, ← inBit_eqN] at hA
    obtain ⟨h₁, e₁, r₁⟩ := RunsLe.toH hA
      (show Avoids nIo (hRdA (nReg r) nIo : Hierarchy.Prog (R + Q + 7) 0) from
        ⟨avoids_clearN (by ndist), ⟨(show nReg r ≠ nIo by ndist), (show nReg r ≠ nIo by ndist)⟩,
          (show nReg r ≠ nIo by ndist), trivial⟩) hd
    have hio := encN_io x (st.set r (inBit x st.pos))
    simp only [NSt.set_pos] at hio
    have hlen := length_nst_le hv
    rcases hl : x.drop st.pos with _ | ⟨a, l⟩
    · have hpx : st.pos = x.length := by
        have := List.drop_eq_nil_iff.mp hl; omega
      have r₂ : RunsLeH (hRdB nXl nIo) (encN x (st.set r (inBit x st.pos)), h₁)
          (encN x (st.set r (inBit x st.pos)), h₁) 2 :=
        RunsLeH.iteF (by simp [tops, hio, hl]) ⟨1, le_rfl, .skip⟩
      refine ⟨h₁, by simp [e₁, hhd]; omega, (r₁.seq r₂).of_eq ?_ ?_⟩
      · congr 2
        ext <;> simp; omega
      · simp only [encN_reg]; exact unitCost_geN (by omega)
    · have r₂ := moveOne_runsH (show (nIo : Fin (R + Q + 7)) ≠ nXl by ndist) (m := 0)
        (s := encN x (st.set r (inBit x st.pos))) (hd := h₁) (a := sym a) (l := bs l)
        (by rw [hio, hl]; rfl)
      have r₂' := r₂.iteT (c := fun t => (t nIo).isSome) (q := skip) (by simp [tops, hio, hl])
      have hlt : st.pos < x.length := by
        by_contra hc; rw [List.drop_eq_nil_of_le (by omega)] at hl; cases hl
      refine ⟨update (update h₁ nIo (h₁ nIo + 1)) nXl (h₁ nXl - 1), ?_,
        (r₁.seq r₂').of_eq ?_ ?_⟩
      · rw [update_of_ne (show (nIo : Fin (R + Q + 7)) ≠ nXl by ndist), update_self, e₁, hhd]
        simp; omega
      · refine Prod.ext ?_ rfl
        have e := encN_advance x (st.set r (inBit x st.pos)) (by simpa using hp)
        simp only [NSt.set_pos, hl, List.tail_cons, List.take_succ_cons, List.take_zero,
          bs_cons, bs_nil, List.singleton_append] at e
        exact e
      · simp only [encN_reg]; exact unitCost_geN (by omega)
  | @rst st hp =>
    have h' := moveAll_runsH (show (nXl : Fin (R + Q + 7)) ≠ nIo by ndist) (m := 0)
      (encN x st nXl) (encN x st) hd rfl
    refine ⟨_, ?_, h'.of_eq (by rw [encN_rst]) ?_⟩
    · simp [hhd]; omega
    · simp only [encN_xl, List.length_reverse, length_bs, List.length_take, unitCost]
      have : min st.pos x.length = st.pos := by omega
      rw [this]; nlinarith
  | @spush q r st hv =>
    have hio : ∀ q : Fin Q, (nStk q : Fin (R + Q + 7)) ≠ nIo := fun q => by ndist
    have hr : nReg r ≠ (nIo : Fin (R + Q + 7)) := by ndist
    have h0 : (nT0 : Fin (R + Q + 7)) ≠ nIo := by ndist
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (nsPush_runs (q := nStk q) (by ndist) (by ndist) (by ndist)
      (encN_reg x st r) (encN_t0 x st))
      (⟨avoids_moveAllN hr h0, hio q, ⟨h0, hr, hio q, hio q⟩, ⟨h0, hr, hio q, hio q⟩⟩) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq ?_ ?_⟩
    · rw [encN_stk, ← bs_append, ← encodeNats_cons, encN_setS]
    · have := length_nst_le hv
      simp only [nst, length_bs] at this
      exact unitCost_geN (by omega)
  | @spop q r st v vs hv hq hvw =>
    have hio : ∀ q : Fin Q, (nStk q : Fin (R + Q + 7)) ≠ nIo := fun q => by ndist
    have hr : nReg r ≠ (nIo : Fin (R + Q + 7)) := by ndist
    have h0 : (nT0 : Fin (R + Q + 7)) ≠ nIo := by ndist
    obtain ⟨hd', e, h'⟩ := RunsLe.toH (nsPop_runs (q := nStk q) (r := nReg r) (by ndist)
      (by ndist) (by ndist) (v := v) (L := bs (encodeNats vs))
      (by rw [encN_stk, hq, encodeNats_cons, bs_append]) (encN_t0 x st))
      (⟨avoids_clearN hr, ⟨hio q, ⟨hio q, h0⟩, ⟨hio q, h0⟩⟩, hio q, avoids_moveAllN h0 hr⟩) hd
    refine ⟨hd', by simp [e, hhd], h'.of_eq ?_ ?_⟩
    · rw [encN_setS]
      have := encN_set x (st.setS q vs) r v
      simpa using this
    · have h1 := length_nst_le hv
      have h2 := length_nst_le hvw
      simp only [nst, length_bs] at h1 h2
      simp only [encN_reg, nst, length_bs]
      exact unitCost_geN (by omega)
  | seq hr₁ _ ih₁ ih₂ =>
    obtain ⟨h₁, e₁, r₁⟩ := ih₁ hpos hd hhd
    obtain ⟨h₂, e₂, r₂⟩ := ih₂ (hr₁.pos_le hpos) h₁ e₁
    exact ⟨h₂, e₂, r₁.seq r₂⟩
  | iteT hc _ ih =>
    obtain ⟨h₁, e₁, r₁⟩ := ih hpos hd hhd
    exact ⟨h₁, e₁, r₁.iteT (by simp only [topsN_enc]; exact hc)⟩
  | iteF hc _ ih =>
    obtain ⟨h₁, e₁, r₁⟩ := ih hpos hd hhd
    exact ⟨h₁, e₁, r₁.iteF (by simp only [topsN_enc]; exact hc)⟩
  | loopF hc => exact ⟨hd, hhd, RunsLeH.loopF (by simp only [topsN_enc]; exact hc)⟩
  | loopT hc hr₁ _ ih₁ ih₂ =>
    obtain ⟨h₁, e₁, r₁⟩ := ih₁ hpos hd hhd
    obtain ⟨h₂, e₂, r₂⟩ := ih₂ (hr₁.pos_le hpos) h₁ e₁
    exact ⟨h₂, e₂, RunsLeH.loopT (by simp only [topsN_enc]; exact hc) r₁ r₂⟩

end Lax119563Proofs.Compiler

end Compiler_NCompile

/-! ### Formerly `Lax119563Proofs.Compiler.Transfer` -/

section Compiler_Transfer

/-!
# Transfer of the pebble game along renumberings with junk vertices

Two pairs of colored graphs `(G₀, G₁)` on `Fin n` and `(G'₀, G'₁)` on `Fin n'`, each pair with a
common color function, are *corresponding* if, after removing a set of *junk* vertices in each
pair (isolated in both graphs of the pair, with colors not used by any other vertex), there is a
bijection of the remaining vertices preserving adjacency in both graphs and the equality of
colors. Then if Duplicator survives `r` rounds of the bijective `m`-pebble game on the first
pair, she survives `r` rounds on the second (`survivesFrom_transfer`).
-/

open Lax119563.ColoredGraphs Lax119563.PebbleGame

namespace Lax119563Proofs.Compiler

/-- The colored graph with vertex set `Fin n`, edges `A` and colors `χ`. -/
abbrev mkGraph (n : ℕ) (A : SimpleGraph (Fin n)) (χ : Fin n → ℕ) : ColoredGraph := ⟨n, A, χ⟩

/-- A pair of graphs on `Fin n` with common colors `χ` and a set `J` of junk vertices. -/
structure JunkPair (n : ℕ) where
  A₀ : SimpleGraph (Fin n)
  A₁ : SimpleGraph (Fin n)
  χ : Fin n → ℕ
  J : Fin n → Prop
  iso₀ : ∀ u v, J u → ¬ A₀.Adj u v
  iso₁ : ∀ u v, J u → ¬ A₁.Adj u v
  col : ∀ u v, J u → ¬ J v → χ u ≠ χ v

namespace JunkPair

variable {n n' : ℕ}

/-- The two graphs. -/
abbrev G₀ (P : JunkPair n) : ColoredGraph := mkGraph n P.A₀ P.χ
/-- The two graphs. -/
abbrev G₁ (P : JunkPair n) : ColoredGraph := mkGraph n P.A₁ P.χ

end JunkPair

/-- A correspondence between the non-junk parts of two junk pairs. -/
structure Corr {n n' : ℕ} (P : JunkPair n) (Q : JunkPair n') where
  f : {u // ¬ P.J u} ≃ {u // ¬ Q.J u}
  adj₀ : ∀ u v : {u // ¬ P.J u}, P.A₀.Adj u.1 v.1 ↔ Q.A₀.Adj (f u).1 (f v).1
  adj₁ : ∀ u v : {u // ¬ P.J u}, P.A₁.Adj u.1 v.1 ↔ Q.A₁.Adj (f u).1 (f v).1
  col : ∀ u v : {u // ¬ P.J u}, P.χ u.1 = P.χ v.1 ↔ Q.χ (f u).1 = Q.χ (f v).1

namespace Corr

variable {n n' : ℕ} {P : JunkPair n} {Q : JunkPair n'}

/-- The inverse correspondence. -/
def symm (C : Corr P Q) : Corr Q P where
  f := C.f.symm
  adj₀ u v := by rw [C.adj₀ (C.f.symm u) (C.f.symm v)]; simp
  adj₁ u v := by rw [C.adj₁ (C.f.symm u) (C.f.symm v)]; simp
  col u v := by rw [C.col (C.f.symm u) (C.f.symm v)]; simp

end Corr

section Mono

variable {m : ℕ} {G H : ColoredGraph}

/-- `S` is obtained from `T` by lifting some pebbles. -/
def SubState (S T : GameState m G H) : Prop := ∀ i, S i = none ∨ S i = T i

lemma SubState.update {S T : GameState m G H} (h : SubState S T) (i : Fin m)
    (x : Option (Fin G.n × Fin H.n)) :
    SubState (Function.update S i x) (Function.update T i x) := by
  intro j
  by_cases hj : j = i
  · subst hj; simp
  · simp only [Function.update_of_ne hj]; exact h j

lemma isPartialIso_sub {S T : GameState m G H} (hT : IsPartialIso G H T) (h : SubState S T) :
    IsPartialIso G H S := by
  intro i j p q p' q' hi hj
  rcases h i with h1 | h1
  · rw [h1] at hi; cases hi
  rcases h j with h2 | h2
  · rw [h2] at hj; cases hj
  exact hT i j p q p' q' (h1 ▸ hi) (h2 ▸ hj)

lemma survivesFrom_sub : ∀ (r : ℕ) {S T : GameState m G H}, SurvivesFrom G H r T →
    SubState S T → SurvivesFrom G H r S
  | 0, _, _, _, _ => trivial
  | r + 1, S, T, hT, h => by
    intro i
    obtain ⟨f, hf⟩ := hT i
    refine ⟨f, fun p => ⟨isPartialIso_sub (hf p).1 (h.update i _), survivesFrom_sub r (hf p).2 (h.update i _)⟩⟩

lemma survivesFrom_of_isEmpty (hG : G.n = 0) (hH : H.n = 0) :
    ∀ (r : ℕ) (S : GameState m G H), SurvivesFrom G H r S
  | 0, _ => trivial
  | r + 1, S => by
    intro i
    have e : Fin G.n ≃ Fin H.n := (finCongr hG).trans (finCongr hH.symm)
    exact ⟨e, fun p => absurd p.2 (by omega)⟩

end Mono

section Transfer

variable {n n' : ℕ} {P : JunkPair n} {Q : JunkPair n'} (C : Corr P Q) {m : ℕ}

/-- Related game states: pebble pairs on non-junk vertices correspond; a lifted pebble may
correspond to a pebble pair `(p', p')` on a junk vertex. -/
def Rel (S : GameState m P.G₀ P.G₁) (S' : GameState m Q.G₀ Q.G₁) : Prop :=
  ∀ i, (∀ p q, S i = some (p, q) → ∃ (hp : ¬ P.J p) (hq : ¬ P.J q),
      S' i = some ((C.f ⟨p, hp⟩ : Fin n'), (C.f ⟨q, hq⟩ : Fin n'))) ∧
    (S i = none → S' i = none ∨ ∃ p', Q.J p' ∧ S' i = some (p', p'))

lemma Rel.update {S : GameState m P.G₀ P.G₁} {S' : GameState m Q.G₀ Q.G₁} (h : Rel C S S')
    (i : Fin m) (x : Option (Fin n × Fin n)) (x' : Option (Fin n' × Fin n'))
    (hx : (∀ p q, x = some (p, q) → ∃ (hp : ¬ P.J p) (hq : ¬ P.J q),
      x' = some ((C.f ⟨p, hp⟩ : Fin n'), (C.f ⟨q, hq⟩ : Fin n'))) ∧
      (x = none → x' = none ∨ ∃ p', Q.J p' ∧ x' = some (p', p'))) :
    Rel C (Function.update S i x) (Function.update S' i x') := by
  intro j
  by_cases hj : j = i
  · subst hj; simpa using hx
  · simp only [Function.update_of_ne hj]; exact h j

lemma Rel.isPartialIso {S : GameState m P.G₀ P.G₁} {S' : GameState m Q.G₀ Q.G₁}
    (h : Rel C S S') (hS : IsPartialIso P.G₀ P.G₁ S) : IsPartialIso Q.G₀ Q.G₁ S' := by
  -- classify the entries of `S'`
  have key : ∀ i p' q', S' i = some (p', q') →
      (∃ p q, S i = some (p, q) ∧ ∃ (hp : ¬ P.J p) (hq : ¬ P.J q),
        p' = (C.f ⟨p, hp⟩ : Fin n') ∧ q' = (C.f ⟨q, hq⟩ : Fin n')) ∨ (Q.J p' ∧ q' = p') := by
    intro i p' q' hi
    rcases hSi : S i with _ | ⟨p, q⟩
    · rcases (h i).2 hSi with h1 | ⟨r, hr, h1⟩
      · rw [h1] at hi; cases hi
      · rw [h1] at hi
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hi)
        exact Or.inr ⟨hr, rfl⟩
    · obtain ⟨hp, hq, h1⟩ := (h i).1 p q hSi
      rw [h1] at hi
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hi)
      exact Or.inl ⟨p, q, rfl, hp, hq, rfl, rfl⟩
  have notJ : ∀ (u : {u // ¬ P.J u}), ¬ Q.J (C.f u : Fin n') := fun u => (C.f u).2
  intro i j p' q' r' t' hi hj
  rcases key i p' q' hi with ⟨p, q, hSi, hp, hq, rfl, rfl⟩ | ⟨hJ, rfl⟩ <;>
  rcases key j r' t' hj with ⟨r, t, hSj, hr, ht, rfl, rfl⟩ | ⟨hJ', rfl⟩
  · obtain ⟨h1, h2, h3⟩ := hS i j p q r t hSi hSj
    refine ⟨?_, ?_, ?_⟩
    · simp only [Subtype.coe_inj, C.f.apply_eq_iff_eq, Subtype.mk.injEq]; exact h1
    · show Q.A₀.Adj _ _ ↔ Q.A₁.Adj _ _
      rw [← C.adj₀ ⟨p, hp⟩ ⟨r, hr⟩, ← C.adj₁ ⟨q, hq⟩ ⟨t, ht⟩]; exact h2
    · show Q.χ _ = Q.χ _
      exact (C.col ⟨p, hp⟩ ⟨q, hq⟩).mp h3
  · refine ⟨?_, ?_, ?_⟩
    · constructor
      · rintro rfl; exact absurd hJ' (notJ _)
      · rintro rfl; exact absurd hJ' (notJ _)
    · show Q.A₀.Adj _ _ ↔ Q.A₁.Adj _ _
      exact ⟨fun h => absurd (Q.iso₀ _ _ hJ' h.symm) id,
        fun h => absurd (Q.iso₁ _ _ hJ' h.symm) id⟩
    · obtain ⟨-, -, h3⟩ := hS i i p q p q hSi hSi
      exact (C.col ⟨p, hp⟩ ⟨q, hq⟩).mp h3
  · refine ⟨?_, ?_, ?_⟩
    · constructor
      · rintro rfl; exact absurd hJ (notJ _)
      · rintro rfl; exact absurd hJ (notJ _)
    · show Q.A₀.Adj _ _ ↔ Q.A₁.Adj _ _
      exact ⟨fun h => absurd (Q.iso₀ _ _ hJ h) id, fun h => absurd (Q.iso₁ _ _ hJ h) id⟩
    · rfl
  · refine ⟨Iff.rfl, ?_, rfl⟩
    show Q.A₀.Adj _ _ ↔ Q.A₁.Adj _ _
    exact ⟨fun h => absurd (Q.iso₀ _ _ hJ h) id, fun h => absurd (Q.iso₁ _ _ hJ h) id⟩

/-- A response of Duplicator that keeps the colors maps non-junk to non-junk vertices. -/
lemma notJ_iff_of_color {g : Fin n ≃ Fin n} (hg : ∀ p, P.χ p = P.χ (g p)) (p : Fin n) :
    ¬ P.J p ↔ ¬ P.J (g p) := by
  constructor
  · intro hp hgp
    exact P.col _ _ hgp hp (hg p).symm
  · intro hgp hp
    exact P.col _ _ hp hgp (hg p)

open Classical in
/-- The transported bijection: `f g f⁻¹` on non-junk vertices, the identity on junk. -/
noncomputable def transport (g : Fin n ≃ Fin n) (hg : ∀ p, ¬ P.J p ↔ ¬ P.J (g p)) :
    Fin n' ≃ Fin n' :=
  Equiv.Perm.subtypeCongr (p := fun u => ¬ Q.J u)
    (C.f.symm.trans ((g.subtypeEquiv hg).trans C.f))
    (Equiv.refl _)

lemma transport_core (g : Fin n ≃ Fin n) (hg : ∀ p, ¬ P.J p ↔ ¬ P.J (g p))
    (u : {u // ¬ P.J u}) :
    transport C g hg (C.f u) = (C.f ⟨g u, (hg u).mp u.2⟩ : Fin n') := by
  classical
  unfold transport
  rw [Equiv.Perm.subtypeCongr.left_apply (p := fun u => ¬ Q.J u) (a := (C.f u : Fin n')) (h := (C.f u).2)]
  simp [Equiv.subtypeEquiv]

lemma transport_junk (g : Fin n ≃ Fin n) (hg : ∀ p, ¬ P.J p ↔ ¬ P.J (g p)) (p' : Fin n')
    (hp' : Q.J p') : transport C g hg p' = p' := by
  classical
  unfold transport
  rw [Equiv.Perm.subtypeCongr.right_apply (p := fun u => ¬ Q.J u) (a := p') (h := not_not.mpr hp')]
  rfl

theorem survivesFrom_transfer :
    ∀ (r : ℕ) (S : GameState m P.G₀ P.G₁) (S' : GameState m Q.G₀ Q.G₁), Rel C S S' →
      SurvivesFrom P.G₀ P.G₁ r S → SurvivesFrom Q.G₀ Q.G₁ r S'
  | 0, _, _, _, _ => trivial
  | r + 1, S, S', hR, hS => by
    intro i
    obtain ⟨g, hg⟩ := hS i
    have hcol : ∀ p, P.χ p = P.χ (g p) := fun p => by
      have := (hg p).1 i i p (g p) p (g p) (by simp) (by simp)
      exact this.2.2
    have hJ := notJ_iff_of_color hcol
    -- the state with pebble `i` lifted
    have hlift : IsPartialIso P.G₀ P.G₁ (Function.update S i none) ∧
        SurvivesFrom P.G₀ P.G₁ r (Function.update S i none) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · refine ⟨?_, survivesFrom_of_isEmpty hn hn r _⟩
        intro j _ p _ _ _ _ _
        exact absurd p.2 (by simp [hn])
      · have hsub : SubState (Function.update S i none)
            (Function.update S i (some (⟨0, hn⟩, g ⟨0, hn⟩))) := by
          intro j
          by_cases hj : j = i
          · subst hj; simp
          · right; simp [Function.update_of_ne hj]
        exact ⟨isPartialIso_sub (hg _).1 hsub, survivesFrom_sub r (hg _).2 hsub⟩
    refine ⟨transport C g hJ, fun p' => ?_⟩
    by_cases hp' : Q.J p'
    · rw [transport_junk C g hJ p' hp']
      have hR' : Rel C (Function.update S i none) (Function.update S' i (some (p', p'))) :=
        hR.update C i none _ ⟨fun _ _ h => (by simp at h), fun _ => Or.inr ⟨p', hp', rfl⟩⟩
      exact ⟨hR'.isPartialIso C hlift.1, survivesFrom_transfer r _ _ hR' hlift.2⟩
    · set u := C.f.symm ⟨p', hp'⟩ with hu
      have hp'u : p' = (C.f u : Fin n') := by simp [hu]
      rw [hp'u, transport_core C g hJ u]
      have hR' : Rel C (Function.update S i (some ((u : Fin n), g u)))
          (Function.update S' i (some ((C.f u : Fin n'),
            (C.f ⟨g u, (hJ u).mp u.2⟩ : Fin n')))) :=
        hR.update C i _ _ ⟨fun p q h => by
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          exact ⟨u.2, (hJ u).mp u.2, rfl⟩, fun h => (by simp at h)⟩
      exact ⟨hR'.isPartialIso C (hg u).1, survivesFrom_transfer r _ _ hR' (hg u).2⟩

end Transfer

end Lax119563Proofs.Compiler

end Compiler_Transfer
