import Lax119563Proofs.Circuits.Bits
import Lax119563Proofs.Programs.RegisterProgram

/-!
# Programs over numeric addresses

The valuation `a` of `s` registers over `𝔽₂^ℓ` is identified with the number `addr a < 2^(s ℓ)`
whose bit `i ℓ + k` is bit `k` of register `i`. An *address program* is a list of commands
over an arbitrary type of locations whose guards are conjunctions of conditions on the
register values `field A (i ℓ) ℓ` and whose updates are XORs with constant masks. Given an
injective numbering of the locations, it compiles to a register program (with the identity
register permutation), and acceptance is preserved (`compile_accepts`).
-/

namespace Lax119563Proofs.Circuits

open Programs

/-- The number with bits `f 0, …, f (n - 1)`. -/
def ofBits : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | n + 1, f => Nat.bit (f 0) (ofBits n fun i => f (i + 1))

lemma testBit_ofBits (n : ℕ) (f : ℕ → Bool) (i : ℕ) :
    (ofBits n f).testBit i = (decide (i < n) && f i) := by
  induction n generalizing f i with
  | zero => simp [ofBits]
  | succ n ih =>
    cases i with
    | zero => simp [ofBits]
    | succ i => simp [ofBits, Nat.testBit_bit_succ, ih]

variable {s ℓ : ℕ}

/-- Bit `p` of the register valuation `a`, for `p < s * ℓ`. -/
def valBit (a : Fin s → Fin ℓ → ZMod 2) (p : ℕ) : Bool :=
  if h : p < s * ℓ then
    decide (a ⟨p / ℓ, Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])⟩
      ⟨p % ℓ, Nat.mod_lt _ (Nat.pos_of_ne_zero fun h0 => by simp [h0] at h)⟩ = 1)
  else false

/-- The address `∑ bit_p 2^p` of a valuation. -/
def addr (a : Fin s → Fin ℓ → ZMod 2) : ℕ := ofBits (s * ℓ) (valBit a)

/-- The numeric value of one register. -/
def regVal (v : Fin ℓ → ZMod 2) : ℕ :=
  ofBits ℓ fun k => if h : k < ℓ then decide (v ⟨k, h⟩ = 1) else false

lemma testBit_addr (a : Fin s → Fin ℓ → ZMod 2) (p : ℕ) :
    (addr a).testBit p = valBit a p := by
  rw [addr, testBit_ofBits]
  unfold valBit
  split_ifs with h <;> simp [h]

lemma addr_lt (a : Fin s → Fin ℓ → ZMod 2) : addr a < 2 ^ (s * ℓ) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_addr, valBit, dif_neg (by omega)]

lemma field_addr (a : Fin s → Fin ℓ → ZMod 2) (i : Fin s) :
    field (addr a) (i * ℓ) ℓ = regVal (a i) := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_field, testBit_addr, regVal, testBit_ofBits]
  by_cases ht : t < ℓ
  · have hlt : t + i * ℓ < s * ℓ := by
      have := i.isLt
      nlinarith
    have hdiv : (t + i * ℓ) / ℓ = i := by
      rw [Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt ht, zero_add]
    have hmod : (t + i * ℓ) % ℓ = t := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
    simp only [valBit, dif_pos hlt, ht, decide_true, Bool.true_and]
    congr 3 <;> simp [hdiv, hmod]
  · simp [ht]

/-- The valuation whose address is `m` (bits beyond `s ℓ` are dropped). -/
def ofAddr (m : ℕ) : Fin s → Fin ℓ → ZMod 2 :=
  fun i k => if m.testBit (i * ℓ + k) then 1 else 0

lemma zmod2_add_eq_one (x y : ZMod 2) :
    decide (x + y = 1) = (decide (x = 1) ^^ decide (y = 1)) := by
  revert x y; decide

lemma addr_add_ofAddr (a : Fin s → Fin ℓ → ZMod 2) {m : ℕ} (hm : m < 2 ^ (s * ℓ)) :
    addr (fun i k => a i k + ofAddr m i k) = addr a ^^^ m := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_xor, testBit_addr, testBit_addr]
  by_cases hp : p < s * ℓ
  · have hℓ : 0 < ℓ := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hp
    have hp' : p / ℓ * ℓ + p % ℓ = p := by rw [Nat.mul_comm]; exact Nat.div_add_mod p ℓ
    simp only [valBit, dif_pos hp, ofAddr, hp', zmod2_add_eq_one]
    congr 1
    split_ifs <;> simp_all
  · have : m.testBit p = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num)
        (not_lt.mp hp)))
    simp [valBit, hp, this]

lemma addr_zero : addr (fun (_ : Fin s) (_ : Fin ℓ) => (0 : ZMod 2)) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [testBit_addr]
  unfold valBit
  split_ifs <;> simp

/-- A command of an address program over locations `L`. The guard `g i v` is a condition
on the value `v` of register `i`. -/
inductive ACmd (L : Type) (s : ℕ)
  | assign (src : L) (g : Fin s → ℕ → Bool) (mask : ℕ) (next : L)
  | fork (src : L) (g : Fin s → ℕ → Bool) (left right : L)

/-- The guard `g` holds at address `A`. -/
def Enabled (ℓ : ℕ) (g : Fin s → ℕ → Bool) (A : ℕ) : Prop :=
  ∀ i : Fin s, g i (field A (i * ℓ) ℓ) = true

/-- Acceptance of an address program with command list `cmds`, accepting location `acc` and
rejecting location `rej`. -/
inductive AAccepts {L : Type} (ℓ : ℕ) (cmds : List (ACmd L s)) (acc rej : L) : L → ℕ → Prop
  | accept (A : ℕ) : AAccepts ℓ cmds acc rej acc A
  | assign {p g m q A} : ACmd.assign p g m q ∈ cmds → p ≠ acc → p ≠ rej → Enabled ℓ g A →
      AAccepts ℓ cmds acc rej q (A ^^^ m) → AAccepts ℓ cmds acc rej p A
  | fork {p g q r A} : ACmd.fork p g q r ∈ cmds → p ≠ acc → p ≠ rej → Enabled ℓ g A →
      AAccepts ℓ cmds acc rej q A → AAccepts ℓ cmds acc rej r A →
      AAccepts ℓ cmds acc rej p A

/-- The register guard of an address guard. -/
def toGuard (g : Fin s → ℕ → Bool) : Guard s ℓ where
  sets i := Finset.univ.filter fun v => g i (regVal v) = true

/-- The register update XOR-ing the address with `m`. -/
def toUpdate (m : ℕ) : Update s ℓ where
  σ := 1
  δ := ofAddr m

/-- The register command of an address command. -/
def ACmd.toCmd {L : Type} {N : ℕ} (code : L → Fin N) : ACmd L s → Command s ℓ N
  | .assign p g m q => .assign (code p) (toGuard g) (toUpdate m) (code q)
  | .fork p g q r => .fork (code p) (toGuard g) (code q) (code r)

/-- Compile an address program to a register program, given an injective numbering of the
locations. -/
def compile {L : Type} (N : ℕ) (code : L → Fin N) (acc rej : L)
    (hne : code acc ≠ code rej) (cmds : List (ACmd L s)) : RegisterProgram s ℓ where
  numLocations := N
  accept := code acc
  reject := code rej
  accept_ne_reject := hne
  commands := cmds.map (ACmd.toCmd code)

lemma toGuard_holds (g : Fin s → ℕ → Bool) (a : Fin s → Fin ℓ → ZMod 2) :
    (toGuard g : Guard s ℓ).Holds a ↔ Enabled ℓ g (addr a) := by
  simp [Guard.Holds, toGuard, Enabled, field_addr]

lemma toUpdate_apply_addr (m : ℕ) (hm : m < 2 ^ (s * ℓ)) (a : Fin s → Fin ℓ → ZMod 2) :
    addr ((toUpdate m : Update s ℓ).apply a) = addr a ^^^ m := by
  rw [← addr_add_ofAddr a hm]
  rfl

/-- All masks of a command list are below `2 ^ (s ℓ)`. -/
def MasksBounded {L : Type} (s ℓ : ℕ) (cmds : List (ACmd L s)) : Prop :=
  ∀ p g m q, ACmd.assign p g m q ∈ cmds → m < 2 ^ (s * ℓ)

lemma compile_accepts_aux {L : Type} {N : ℕ} {code : L → Fin N}
    (hcode : Function.Injective code) {acc rej : L} (hne : code acc ≠ code rej)
    {cmds : List (ACmd L s)} (hmask : MasksBounded s ℓ cmds)
    (q : Fin (compile (ℓ := ℓ) N code acc rej hne cmds).numLocations)
    (a : Fin s → Fin ℓ → ZMod 2) (h : (compile (ℓ := ℓ) N code acc rej hne cmds).Accepts q a) :
    ∀ p, code p = q → AAccepts ℓ cmds acc rej p (addr a) := by
  induction h with
  | accept a =>
    intro p hq
    have : p = acc := hcode hq
    subst this
    exact AAccepts.accept _
  | assign hmem hpa hpr hg _ ih =>
    intro p hq
    obtain ⟨c, hc, hceq⟩ := List.mem_map.mp hmem
    cases c with
    | assign p' g' m' q' =>
      simp only [ACmd.toCmd] at hceq
      injection hceq with h1 h2 h3 h4
      subst h2 h3 h4
      have : p' = p := hcode (h1.trans hq.symm)
      subst this
      clear h1
      refine AAccepts.assign hc (fun h => hpa (by rw [← hq, h]; rfl))
        (fun h => hpr (by rw [← hq, h]; rfl)) ((toGuard_holds _ _).mp hg) ?_
      rw [← toUpdate_apply_addr m' (hmask _ _ _ _ hc)]
      exact ih q' rfl
    | fork => simp [ACmd.toCmd] at hceq
  | fork hmem hpa hpr hg _ _ ih₁ ih₂ =>
    intro p hq
    obtain ⟨c, hc, hceq⟩ := List.mem_map.mp hmem
    cases c with
    | assign => simp [ACmd.toCmd] at hceq
    | fork p' g' q' r' =>
      simp only [ACmd.toCmd] at hceq
      injection hceq with h1 h2 h3 h4
      subst h2 h3 h4
      have : p' = p := hcode (h1.trans hq.symm)
      subst this
      clear h1
      exact AAccepts.fork hc (fun h => hpa (by rw [← hq, h]; rfl))
        (fun h => hpr (by rw [← hq, h]; rfl)) ((toGuard_holds _ _).mp hg) (ih₁ q' rfl)
        (ih₂ r' rfl)

/-- Compilation preserves acceptance. -/
theorem compile_accepts {L : Type} {N : ℕ} {code : L → Fin N} (hcode : Function.Injective code)
    {acc rej : L} (hne : code acc ≠ code rej) {cmds : List (ACmd L s)}
    (hmask : MasksBounded s ℓ cmds) (p : L) (a : Fin s → Fin ℓ → ZMod 2) :
    (compile (ℓ := ℓ) N code acc rej hne cmds).Accepts (code p) a ↔
      AAccepts ℓ cmds acc rej p (addr a) := by
  constructor
  · intro h
    exact compile_accepts_aux hcode hne hmask _ a h p rfl
  · intro h
    generalize hA : addr a = A at h
    induction h generalizing a with
    | accept A => exact RegisterProgram.Accepts.accept _
    | assign hc hpa hpr hg _ ih =>
      subst hA
      refine RegisterProgram.Accepts.assign (List.mem_map.mpr ⟨_, hc, rfl⟩)
        (fun h => hpa (hcode h)) (fun h => hpr (hcode h)) ((toGuard_holds _ _).mpr hg) ?_
      exact ih _ (toUpdate_apply_addr _ (hmask _ _ _ _ hc) a)
    | fork hc hpa hpr hg _ _ ih₁ ih₂ =>
      subst hA
      exact RegisterProgram.Accepts.fork (List.mem_map.mpr ⟨_, hc, rfl⟩)
        (fun h => hpa (hcode h)) (fun h => hpr (hcode h)) ((toGuard_holds _ _).mpr hg)
        (ih₁ a rfl) (ih₂ a rfl)

end Lax119563Proofs.Circuits

namespace Lax119563Proofs.Circuits

/-! ## Field guards and field updates -/

variable {s : ℕ}

/-- The guard `field A k m = q`, split into conditions on the registers of width `ℓ`. -/
def fieldGuard (ℓ k m q : ℕ) : Fin s → ℕ → Bool :=
  fun i v => decide (∀ t < m, (k + t) / ℓ = i → v.testBit ((k + t) % ℓ) = q.testBit t)

lemma enabled_fieldGuard {ℓ k m q A : ℕ} (hℓ : 0 < ℓ) (hkm : k + m ≤ s * ℓ) (hq : q < 2 ^ m) :
    Enabled ℓ (fieldGuard (s := s) ℓ k m q) A ↔ field A k m = q := by
  rw [field_eq_iff hq]
  have key : ∀ t, (k + t) % ℓ + (k + t) / ℓ * ℓ = k + t := fun t => by
    rw [Nat.mul_comm]; exact Nat.mod_add_div _ _
  constructor
  · intro h t ht
    have hlt : (k + t) / ℓ < s := Nat.div_lt_of_lt_mul (by nlinarith)
    have := h ⟨_, hlt⟩
    simp only [fieldGuard, decide_eq_true_eq] at this
    have h2 := this t ht rfl
    rw [testBit_field, key] at h2
    simpa [Nat.mod_lt _ hℓ, Nat.add_comm t k] using h2
  · intro h i
    simp only [fieldGuard, decide_eq_true_eq]
    intro t ht hi
    rw [testBit_field, ← hi, key]
    simpa [Nat.mod_lt _ hℓ, Nat.add_comm k t] using h t ht

/-- The mask replacing a field with current value `q` by `v`. -/
def fieldMask (k q v : ℕ) : ℕ := (q ^^^ v) <<< k

lemma xor_fieldMask {A k m q v : ℕ} (h : field A k m = q) :
    A ^^^ fieldMask k q v = setBits A k m v := by
  rw [fieldMask, setBits, h]

lemma fieldMask_lt {k m q v N : ℕ} (hq : q < 2 ^ m) (hv : v < 2 ^ m) (hkm : k + m ≤ N) :
    fieldMask k q v < 2 ^ N := by
  rw [fieldMask, Nat.shiftLeft_eq]
  have h1 : q ^^^ v < 2 ^ m := Nat.xor_lt_two_pow hq hv
  calc (q ^^^ v) * 2 ^ k < 2 ^ m * 2 ^ k := Nat.mul_lt_mul_of_pos_right h1 (by positivity)
    _ = 2 ^ (k + m) := by rw [← pow_add, Nat.add_comm]
    _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hkm

end Lax119563Proofs.Circuits
